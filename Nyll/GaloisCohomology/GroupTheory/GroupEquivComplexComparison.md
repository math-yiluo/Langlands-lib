# Transport of cochain, chain and Tate complexes along a group isomorphism

Module `Nyll.GaloisCohomology.GroupTheory.GroupEquivComplexComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Given rings and groups in one universe `u`, a group isomorphism `e : G ≃* H`, representations `A` of `G` and `B` of `H` over a commutative ring `R`, and an `R`-linear equivalence `l : A ≃ B` that is equivariant in the sense `l ∘ ρ_A(g) = ρ_B(e g) ∘ l` for all `g` (hypothesis `hl`), the file builds isomorphisms of the actual complexes computing group cohomology, group homology and Tate cohomology, and hence of the Tate cohomology groups in every degree.

## Main definitions and results

- `Rep.groupEquiv_inverse_comm`: `l⁻¹` is equivariant for `e⁻¹`.
- `Rep.groupEquiv_norm`: for finite `G` and `H`, `l` carries the norm element `N_G a` to `N_H (l a)`.
- `groupCohomology.groupEquivComplexIso`: an isomorphism of inhomogeneous cochain complexes, built from Mathlib's `cochainsMap` along `e⁻¹` with coefficient map `l`. On an `n`-cochain it is `f ↦ (h ↦ l (f (e⁻¹ ∘ h)))` (`groupEquivComplexIso_hom_f_apply`, with the inverse formula alongside).
- `groupHomology.groupEquivComplexIso`: an isomorphism of inhomogeneous chain complexes, built from `chainsMap` along `e`; it sends the generator `single g a` to `single (e ∘ g) (l a)`.
- `TateCohomology.groupEquiv_tateNorm`: for finite groups, the two comparisons commute with the Tate norm map from degree −1 to degree 0.
- `TateCohomology.groupEquivComplexIso`: an isomorphism `tateComplex A ≅ tateComplex B`, equal to the cochain comparison in degrees `n ≥ 0` and to the chain comparison in degrees `−(n+1)`; formulas for its components are recorded.
- `TateCohomology.groupEquivIso n`: the induced isomorphism of Tate cohomology groups `Ĥⁿ(G, A) ≅ Ĥⁿ(H, B)` for every integer `n`.

## Proofs

The complex isomorphisms are checked componentwise by evaluating on cochains and on `Finsupp.single` generators. The Tate complex isomorphism is assembled degree by degree with `HomologicalComplex.Hom.isoOfComponents`; the only non-formal square is the one at the Tate norm, which is `groupEquiv_tateNorm` and rests on `groupEquiv_norm`.

## Points to watch

- Everything lives in a single universe `u` for `R`, `G`, `H` and the representations.
- The Tate statements need `G` and `H` finite (`Fintype`).
- The cochain map goes along `e⁻¹` while the chain map goes along `e`; both use the same `l`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/GroupEquivComplexComparison.lean`: the Lean file is the source byte for byte (SHA-256 `f89d4ad19b37af8a6a285e77d736f86f58006278a7bedb4b7603b80cecd63ac1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
