# Images of a normal extension in an ambient field

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.NormalFieldRange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The image of a normal extension in a larger field does not depend on the embedding.

- `AlgHom.fieldRange_eq_of_normal`: if L/F is normal and f, g : L → Ω are two F-algebra embeddings into a field Ω, then f and g have the same image as intermediate fields of Ω/F.

Each image is contained in the other. The image of g is normal over F, so the embedding f ∘ g⁻¹ of the image of g into Ω, by Mathlib's `AlgHom.fieldRange_of_normal`, has image equal to the image of g; and that image is the image of f.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/NormalFieldRange.lean`: the Lean file is the source byte for byte (SHA-256 `9e5b66d0b14d96b6c8ae6e815b1c41045eeb5bf9737f94b769e18fd232e246c5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
