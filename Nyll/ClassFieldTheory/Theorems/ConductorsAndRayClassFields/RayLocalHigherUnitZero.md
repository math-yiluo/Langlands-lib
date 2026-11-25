# The higher unit group of depth zero

Module `Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayLocalHigherUnitZero`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K and a finite place `v` of K (a height-one prime of 𝓞_K), the library defines higher unit groups `rayLocalHigherUnitGroup v n` inside the completion K_v.

`rayLocalHigherUnitGroup_zero`: at depth zero this group is the group of units of the ring of integers of K_v (`v.adicCompletionIntegers K`), not the whole multiplicative group of K_v.

The proof unfolds the definition to the ray-class version `RayClass.localHigherUnitGroup` and uses the corresponding statement there.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayLocalHigherUnitZero.lean`: the Lean file is the source byte for byte (SHA-256 `9264051c288dd06d65a76120c34cbc1316ece69a81015331ae10823b4ced0630`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
