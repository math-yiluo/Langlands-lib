# Two models of the residue field of a finite fixed field

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field and `E ⊆ SeparableClosure K` the fixed field of a closed subgroup `H` of finite index. The library sees the residue field of `E` in two ways. One is intrinsic, inside a selected residue field of a valuation ring of `SeparableClosure K`, through decomposition fields; the residue-degree datum `localResidueDatum K` uses this one. The other is the literal residue field of the valuation ring of `E`, used in the norm formula. This file identifies the two and concludes that the abstract residue degree of `H` is the ordinary residue degree `[k_E : k_K]`.

## Main definitions and results

- `valuationSubringEquivDecompositionFieldOfEqTop`: for a Galois extension `Ω / F`, a valuation ring `A` of `Ω` whose restriction to `F` is `C`, and decomposition group of `A` equal to the whole Galois group, a ring isomorphism from `C` to the valuation ring of the decomposition field (which is then `F` itself).
- `residueFieldEquivDecompositionResidueOfEqTop`: the induced isomorphism from the residue field of `C` to `decompositionResidueField F A`; `residueFieldEquivDecompositionResidueOfEqTop_algebraMap` shows it is compatible with reduction into the selected residue field.
- `localResidueDatum_residueDegree_eq_residueFinrank`: for a finite abstract field `H`, not necessarily normal over `K`, whose fixed field `E` carries a nonarchimedean local field structure with valuation extending that of `K`, the residue degree of `H` for `localResidueDatum K` equals `Module.finrank 𝓀[K] 𝓀[E]`.

## Proof

The restriction to `E` of the chosen valuation ring `localSeparableValuationSubring K` is the valuation ring of `E`, by uniqueness of the extended valuation on a finite separable extension (`ValuationSubring.restrictIntermediateField_eq_of_finite_separable`). The decomposition group over `E` is everything (`localAbstractFixedDecompositionGroup_eq_top`), so the isomorphisms above apply. They are compatible with the inclusions of the residue field of `K`, and `Algebra.finrank_eq_of_equiv_equiv` transfers the degree computed in `localResidueDatum_residueDegree_eq_selectedResidueFinrank`.

## Points to watch

- Finite-dimensionality of `E` over `K` (`[FiniteDimensional K E]`, asked for besides the finite index bundled in `H`), the valuative relation, topology, local-field structure and valuation extension on `E` are instance hypotheses of the main theorem; they are not constructed here.
- The residue degree on the right uses the module structure `IsLocalRing.ResidueField.instModule`, written explicitly in the statement.
- `K` may lie in any universe; the general isomorphisms allow `F` and `Ω` in different universes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean`: the Lean file is the source byte for byte (SHA-256 `34bad522d0f5b0350541246e7fdc8c4141c2756a07000c0c4ebab2bb5c9d25fe`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
