# Recovering actual solutions from an fppf refinement

This module is the fppf analogue of the published module
`Langlands.GroupScheme.Descent.ReverseRefinement`. All schemes lie in an
arbitrary universe `u`.

- `Solution.descendIsoOfFppf s t e he`: here `s : Solution D` and
  `t : Solution E` are solutions of data over an fppf surjection
  `p : S ⟶ B`, and `e : G ≅ H` is a compatible isomorphism of the groups over
  `S`. The forward map is `descendHomOfFppf` (module `FppfHomDescent`). Its
  base change is the isomorphism `s.iso ≪≫ e ≪≫ t.iso.symm`, so
  `isoOfFppfBaseChange` (module `FppfReflection`) shows that it is
  invertible. `baseChange_descendIsoOfFppf` is the recovery square.

Now let `D : Datum p G` with `p : S ⟶ B` arbitrary, and let `q : V ⟶ S` be a
map whose composite `q ≫ p` is surjective, flat and locally of finite
presentation. Let `s : Solution (D.refine q)` be a solution of the refined
datum, with descended group `C = s.obj`.

- `fppfRefinementComparison q s : p*C ≅ G`. On the cross overlap
  `W = V ×_B S`, the published `refinementSolutionOnCover` and
  `transitionSolution` are two solutions of the same datum along the second
  projection `r : W ⟶ S`. Their descended groups are `p*C` and `G`. The map `r`
  is a base change of `q ≫ p`, hence an fppf surjection, and `descendIsoOfFppf`
  applied to the identity gives the comparison.
- `fppfRefinementComparison_baseChange` describes the comparison on `W`. It is
  the square comparison `r*(p*C) ≅ v*((q ≫ p)*C)`, then `v*s.iso`, then the
  comparison `v*(q*G) ≅ (v ≫ q)*G`, then the transition of `D` from `v ≫ q` to
  `r`. `fppfRefinementComparison_restrict` proves the same formula after
  pullback to any test scheme over `W`. It uses `pullbackComparison`
  naturality and associativity, `map_transition` and the published
  `squareComparison_pullback`. `fppfRefinementComparison_local` applies this
  to the map into `W` given by a commuting pair.
- `fppfRefinementComparison_transition`: for two maps `f, g` to `S` that share
  one `V`-coordinate, the comparison commutes with the transitions of `D` and
  of the canonical datum. The proof combines the local formula at both ends,
  `transition_comp`, and the published
  `canonicalDatum_transition_squareComparison`.
- `fppfRefinementComparison_compatible`: compatibility on the original overlap.
  Let `z : Z = V ×_B (S ×_B S) ⟶ S ×_B S` be the pullback of `q ≫ p` along the
  map to `B`. The previous item gives compatibility after `pullHom z`. Since
  `z` is an fppf surjection, `baseChange z` is faithful, which gives
  compatibility on `S ×_B S` after cancelling the endpoint comparisons.
- `fppfSolutionOfRefinement q s : Solution D` has object `C`, isomorphism
  `fppfRefinementComparison q s` and the compatibility above.

No surjectivity of `q`, affineness or quasi-compactness is needed. Provenance
is internal: these are the published étale arguments with the fppf descent of
`FppfHomDescent` and `FppfReflection`.
