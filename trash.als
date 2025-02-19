var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and       // guard
  after no Trash and   // effect on Trash
  File' = File - Trash // effect on File
}

pred delete [f : File] {
  not (f in Trash)   // guard
  Trash' = Trash + f // effect on Trash
  File' = File       // frame condition on File
}

pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}
pred permDelete [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File - f   // effect on File
}

pred directDelete [f : File] {
  not (f in Trash)  // guard
  Trash' = Trash    // frame condition on Trash
  File' = File - f  // effect on File
}

pred duplicate [f : File] {
  let newFile = File' - File | {
    one newFile      // Ensure a single new file is created
    Trash' = Trash   // frame condition on Trash
    File' = File + newFile // Add new file to File
  }
}
fact trans {
  always (empty or (some f : File | delete[f] or restore[f]or permDelete[f] or directDelete[f] or duplicate[f]))
}

run example {}
