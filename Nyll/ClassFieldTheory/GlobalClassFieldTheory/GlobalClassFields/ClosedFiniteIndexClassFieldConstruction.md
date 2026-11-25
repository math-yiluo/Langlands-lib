# Construction of the class field of a closed finite-index subgroup

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldConstruction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K` and a closed subgroup `H` of finite index in the idele class group `C_K`, this file fixes the data from which the library's class field of `H` is built. All definitions are reducible abbreviations of imported constructions.

- `closedFiniteIndexClassFieldNormAmbient H hclosed`: a finite Galois extension of `K` whose norm group lies in `H` (`closedFiniteIndexClassFieldNormAmbient_normRange_le`, from an imported existence result).
- `closedFiniteIndexClassFieldBaseSubgroup`, `closedFiniteIndexClassFieldReciprocityFiniteAbstractField`, `closedFiniteIndexClassFieldSubextension`: the corresponding data in the abstract class formation over the absolute Galois group of `ℚ` (automorphisms of `SeparableClosure ℚ`); the last is a finite abelian subextension determined by `H`.
- `closedFiniteIndexClassFieldBase`: a fixed-field copy of `K`, with `closedFiniteIndexClassFieldBaseEquiv : K ≃ₐ[ℚ] closedFiniteIndexClassFieldBase`.
- `closedFiniteIndexClassField H hclosed`: the class field of `H`.

The class field and its base live in `Type` and are extensions of the copy of `K`, not of `K` itself. That the norm group is exactly `H`, and the reciprocity statements, are proved in other files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldConstruction.lean`: the Lean file is the source byte for byte (SHA-256 `dcf59d546807ba804fa0f5ddbe7eb3dcbce7a5e51834c1b09418fb958b1934e4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
