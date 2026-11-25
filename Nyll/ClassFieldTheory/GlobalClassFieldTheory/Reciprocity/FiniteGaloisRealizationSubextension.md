# A finite Galois tower L/K as an abstract finite Galois subextension

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationSubextension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields, realized inside ℚ̄ = `SeparableClosure ℚ` by the compatible embeddings of the library, with closed subgroups J ≤ H of Gal(ℚ̄/ℚ) fixing the copies of L and K. This file packages the pair as the data used by the library's abstract reciprocity: a finite abstract field H and a finite Galois subextension J of it. It identifies the abstract quotient with Gal(L/K).

## Main definitions and results

- `numberFieldTowerExtensionSubgroup_normal` and `numberFieldTowerExtensionQuotient_finite`: the extension subgroup of J in H is normal with finite quotient. Both are specializations of the library's ambient-embedding results.
- `numberFieldTowerFiniteGaloisSubextension K L : FiniteGaloisSubextension H`, with J as its field.
- `numberFieldTowerFiniteAbstractField K L : FiniteAbstractField`: H with its finite-index witness. `numberFieldTowerBaseSubgroup_isOpen`: H is open in Gal(ℚ̄/ℚ).
- `numberFieldTowerExtensionQuotientEquivGaloisGroup K L`: the abstract extension quotient is isomorphic to Gal(L/K). On the class of σ ∈ Gal(ℚ̄/K), carried into H by `numberFieldTowerSeparableClosureEquivBaseSubgroup`, it gives `AlgEquiv.restrictNormalHom L σ`, the restriction of σ to L (`..._mk_baseSubgroupEquiv`).
- `numberFieldTowerFiniteAbelianSubextension K L`: for `IsAbelianGalois K L`, the same subextension bundled as a `FiniteAbelianSubextension`. Commutativity of the quotient is pulled back from Gal(L/K) through the isomorphism.

## Points to watch

- All objects depend on the chosen embedding of L into ℚ̄, with K embedded through L. The K-algebra structure on ℚ̄ used in the restriction statement is supplied by `let`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FiniteGaloisRealizationSubextension.lean`: the Lean file is the source byte for byte (SHA-256 `520b8b2007a98410a1dae270ef8cce71cb559f50d524573de4fcb5a815dc5b62`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
