# Residue action on the whole Galois group and image indices

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a Galois extension `L/K` and a valuation ring `A` of `L` whose decomposition group is all of `Gal(L/K)`, the residue action of the decomposition group is viewed as an action of the whole Galois group, and the index of a subgroup's image under the resulting degree map is computed.

- `toDecompositionGroupOfEqTop`: when `decompositionGroup K A = ⊤`, every automorphism as a decomposition-group element.
- `residueAlgActionOfEqTop`: the action of `Gal(L/K)` on the residue field of `A`; `residueAlgActionOfEqTop_surjective`: it is surjective.
- `residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup`: for a finite field `k` and an algebraically closed algebraic extension `Ω`, if `ρ : G → Gal(Ω/k)` maps a subgroup `H` onto the fixing group of a finite Galois intermediate field `E`, then the image of `H` under `residueAbsoluteDegreeIn ∘ ρ` has index `[E : k]`.

The ambient field is meant to be the separable closure: an algebraic closure need not be Galois over an imperfect local field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean`: the Lean file is the source byte for byte (SHA-256 `4934efabe0ea24243391fd25aaef2f2eb777be6458c4c0638f39237495c98eac`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
