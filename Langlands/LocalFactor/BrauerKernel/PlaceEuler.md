# Local L-factors and epsilon factors of a global relation at a finite place

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global argument
(1973, proof of Lemma 4.12) the local relation at each finite place makes the local L-factors of
the global product cancel, and the remaining epsilon factors are compared place by place. This
unit connects the local relation (`BrauerKernel.PlaceEpsilon.LocalPlaceRelation`) with the local
factors of the published Brauer product package (`hasGlobalEquation_brauerProduct`). It is
bookkeeping with published lemmas and has no separate literature source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`; notation as in `PlaceEpsilon`.

## Results

- `placeLFactorProduct r K Λ₁ Λ₂ z s`: the product over the pairs `(j, u)`, `u` a place of `K j`
  above `z`, of `(L(s, (Λ₁ j)_u) / L(s, (Λ₂ j)_u)) ^ r_j` with the Hecke L-factors `heckeL`.
- `prod_heckeL_eq_placeLFactorProduct`: the local factor of the Brauer product at `z` (a product over
  `j` of quotients of products over the places above `z`, raised to `r_j`) is this regrouped
  product (`Fintype.prod_sigma`, `placesAbove` as the image of the places above `z`).
- `placeLFactorProduct_eq_one`: if the local relation at `z` holds for a normalized family of `k_z`,
  the regrouped product is `1` wherever all the L-factors involved are nonzero. Proof: the
  transported candidates are geometric (clause 2 of the published
  `commonClosureGeometricProof`); `prod_lFactor_eq_one_of_relation` (`BrauerKernel.LocalEuler`)
  applies, and `lFactor_quasicharacterAt` identifies Tate's L-factors on the canonical packages with
  `heckeL`.
- `prod_heckeL_eq_one_of_ne_zero`: if moreover all weights `r_j` are nonzero, the local factor of the
  Brauer product at `z` is `1` as soon as it is nonzero: a nonzero product of `r_j`-th powers of
  quotients has nonzero numerators and denominators.
- `weilCharacter_quasicharacterAt_inv`, `localPlaceRelation_inv` (**dual relation**): the
  contragredient (`ExactGrothendieckGroup.continuousDual`) commutes with induction
  (`continuousDual_continuousInduceAlong`) and inverts character classes
  (`continuousDual_characterClass`), so the local relation for `Λ₁`, `Λ₂` gives the local relation
  for `Λ₁⁻¹`, `Λ₂⁻¹`.
- `prod_finiteEpsilon_eq_placeEpsilonRatioProduct`: the epsilon factor of the Brauer product at `z`
  and `s = 0`, for additive components `ψf` of a global character with `ψf z` the completion-topology
  reading of `ψz` and self-dual measures `μK`, is `placeEpsilonRatioProduct` for `ψz` and the
  transported measures. Proof: the published `prod_epsilon_quasicharacterAt_eq_prod_finiteEpsilon`
  and regrouping.
