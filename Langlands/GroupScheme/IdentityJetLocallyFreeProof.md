# Identity jets of smooth separated groups are locally finite free

Worker 946, Task 7782.

This module proves `Langlands.GroupScheme.IdentityJetLocallyFreeStatement`
with no hypotheses: `Langlands.GroupScheme.identityJetLocallyFree`. It uses
the affine chart description of identity jets in
`Langlands.GroupScheme.IdentityJetAffineChart` and the jet base-change square
of `Langlands.GroupScheme.MatrixRepresentation.LocalCentralKernelReduction`.

## Localization to a free algebra

`IdentityJet.exists_free_jet_localization` works over `Spec R`. Let `G` be
smooth and separated, and `V` an affine open containing the unit section.
Then `chartJetAlgebra G n V` is a finite projective `R`-module (proved in the
chart module), hence finitely presented. Its free locus is all of
`Spec R` (Mathlib's `Module.freeLocus_eq_univ_iff`), so it is free at every
prime `t`. Mathlib's `Module.FinitePresentation.exists_free_localizedModule_powers`
gives `r ∉ t` such that the localization at `r` is free over `R_r`. Then
`R_r` is nontrivial, as it maps to the local ring at `t`.

Let `j : Spec R_r ⟶ Spec R` be the localization map and `G'` the base change
along `j`. The jet of `G'` is the pullback of the jet of `G` along `j`. This
comes from pasting `IdentityJet.jetBaseChange_isPullback` with the defining
pullback of `G'`. The chart isomorphism turns the jet of `G` into `Spec P`
over `Spec R`, and Mathlib's `pullbackSpecIso` identifies the pullback with
`Spec (R_r ⊗[R] P)`. The isomorphism is compatible with the projections
(`pullbackSpecIso_hom_fst'`). Finally, `R_r ⊗[R] P` is isomorphic to the
localized module (`LocalizedModule.isBaseChange`), so it is free of finite
rank. `Module.finBasis` gives a basis indexed by `Fin m`.

## Jets of isomorphic groups

- `IdentityJet.ideal_comap_le_of_hom`: a homomorphism `f : H ⟶ H'` of group
  schemes pulls the jet ideal of `H'` into the jet ideal of `H`, because it
  preserves the unit section.
- `IdentityJet.homJetMap f n` is the induced morphism of jets, compatible with
  inclusions and projections (`homJetMap_inclusion`, `homJetMap_projection`).
- `IdentityJet.jetIsoOfIso` turns an isomorphism of group schemes into an
  isomorphism of jets. The two composites are the identity because the jet
  inclusions are monomorphisms.

## Assembly

- `IdentityJet.exists_free_jet_affine`: over `Spec R` and at any point `t`,
  choose an affine open `V` of the group containing the unit at `t`. Choose a
  basic open `D(f) ∋ t` inside the preimage of `V` under the unit section.
  Base change along `Spec R_f ⟶ Spec R`. The preimage of `V` is affine (the
  projection is an affine morphism) and contains the whole unit section. Then
  apply the localization step at a point over `t`. The composite of the two
  localization maps is an open immersion whose image contains `t`. The jet
  of the iterated base change is compared with the jet of the base change
  along the composite by `jetIsoOfIso` applied to the Library's
  `Descent.pullbackComparison`.
- `identityJetLocallyFree`: given `s ∈ W`, Mathlib's
  `Scheme.exists_affine_mem_range_and_range_subset` gives an open immersion
  `Spec R₁ ⟶ S` with image containing `s` and contained in `W`. The previous
  step applies to the base-changed group at a point over `s`, and the same
  comparison transports the result to the composite open immersion.

The module adds no geometric input beyond Mathlib and the Library modules
named above.
