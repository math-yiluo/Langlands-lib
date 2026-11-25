# The residue degree datum of a finite field

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueDatum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite field `k` and an algebraically closed algebraic extension `Ω`, the degree map `Gal(Ω/k) → ZHat` given by arithmetic Frobenius becomes the initial datum of the abstract class formation, and the image of each finite level is computed.

- `residueDatumIn k Ω`: the `DegreeData` whose degree is `residueAbsoluteDegreeIn k Ω`, surjective because it is the inverse of an isomorphism.
- `residueDatumIn_fieldImage_closedFixingSubgroup`: for a finite Galois intermediate field `E`, the degree image of the subgroup fixing `E` is `n·ZHat` with `n = [E : k]`. An automorphism fixes `E` exactly when its degree reduces to `0` modulo `n`.
- `Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup`: hence this image has index `[E : k]`, so the abstract residue degree is the field degree.

The index statement sits in an `Internal` namespace. `DegreeData` is the library's own notion.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean`: the Lean file is the source byte for byte (SHA-256 `ae026efed3d165834335efcb8e2b92c9f497ca05119a56e908eb44846f4fa833`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
