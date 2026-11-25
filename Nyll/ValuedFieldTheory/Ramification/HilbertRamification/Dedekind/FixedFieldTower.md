# The tower Z_P ⊆ T_P ⊆ L

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFieldTower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite group `G` that is a Galois group of `L/K` and also acts on a ring `B`, and a prime `P` of `B`, this file studies the tower formed by the decomposition field `Z_P` and the inertia field `T_P` of the previous file. It shows that `L/Z_P` is Galois with group `G_P`, that `T_P/Z_P` is Galois with group `G_P/I_P`, and that this group is the residue automorphism group.

## Main definitions and results

- `inertiaFieldOverDecompositionField G P`: `T_P` as an intermediate field of `L` over `Z_P`; restricting scalars back to `K` gives `T_P`.
- `dedekindTower_decompositionGroupEquivGalDecompositionField`: `G_P ≃* Gal(L/Z_P)`, acting through the original action; `L/Z_P` is finite-dimensional and Galois.
- `inertiaGroupOverDecompositionField`: the image of `I_P` in `Gal(L/Z_P)`; it is normal, its fixed field is `T_P`, and it is the subgroup fixing `T_P`.
- `inertiaFieldOverDecompositionField_isGalois`: `T_P/Z_P` is Galois.
- `dedekindRamification_decompositionQuotientInertiaEquivGalInertiaFieldOverDecomposition`: `G_P/I_P ≃* Gal(T_P/Z_P)`; hence `[T_P : Z_P] = |G_P/I_P|`.
- `dedekindRamification_galInertiaFieldOverDecompositionEquivResidueGalois`: for `P` prime over `p` of `A`, with the action on `B` commuting with `A` and `A → B` invariant under `G`, `Gal(T_P/Z_P)` is isomorphic to the group of `(A/p)`-automorphisms of `B/P`.
- `dedekindInertiaField_inertiaField_properties`: in one statement, `T_P/Z_P` is Galois, such an isomorphism exists, and the subgroup of `G` fixing `T_P` is `I_P`.

The quotient isomorphism uses Mathlib's `IsGalois.normalAutEquivQuotient`; the residue comparison composes it with the residue exact sequence of the Dedekind layer.

The actions of `G` on `B` and on `L` are not required to be compatible, so the link between `T_P/Z_P` and the residue extension passes only through the subgroups `G_P` and `I_P` of `G`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Dedekind/FixedFieldTower.lean`: the Lean file is the source byte for byte (SHA-256 `429b252202f28df9dec5fc77414377a53385d116061312e8b042e76a919d1282`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
