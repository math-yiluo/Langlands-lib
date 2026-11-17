# Independence of pinned comparisons in a fixed inner class

This is an internal categorical consequence of the actual pinned-comparison
rigidity in `AffinePinnedInnerUniqueness`. It introduces no new geometric
existence assumption and cites no additional literature.

For supplied affine pinned models `M` and `N`, any common scheme `T`, maps
`f : T ⟶ M.base` and `g : T ⟶ N.base`, an original comparison `e`, and any
map `p : V ⟶ T`, let `d` be a comparison over `p ≫ f` and `p ≫ g`.
`PinnedComparisonIndependence` asserts that, if `d` is fppf-locally pinned
and inner-equivalent to the normalized pullback of `e`, its associated
`comparisonLocalIso p d` is independent of the cover point on every relative
scheme test. The theorem `pinnedComparisonIndependence` proves this assertion
in arbitrary universe `u`. Flatness, surjectivity and local finite
presentation of `p` are not required for this independence result.

The concrete constructions and proof are as follows.

- `testPointsEquiv f W` identifies sections of the direct pullback along
  `W.hom ≫ f` with `W`-points of `M.groupOver f`. It composes the two existing
  multiplicative pullback-point equivalences. `testPointsEquiv_fst` records
  its first projection to the original group scheme.
- Fppf-local pinning and inner equivalence survive pullback with specified
  equal endpoints. `pullComparisonAlong_pullComparison` uses the existing
  tower coherence to identify a pullback through a cover point with the
  direct pullback along the underlying relative test.
- `comparisonAtCoverPoint p d a` pulls `d` along the underlying map of a
  point `a : W ⟶ Over.mk p`, with endpoints explicitly identified as
  `W.hom ≫ f` and `W.hom ≫ g`.
- `comparisonAtCoverPoint_toFun` identifies evaluation of this direct
  comparison with the local all-test map of `d`, under `testPointsEquiv`.
  The proof compares the two lifts into the direct source pullback by its
  two projections. The first uses the original-group projection identities
  for the pullback comparisons; the second uses the structure-map equations
  of the actual morphisms over the cover. The target projection is then
  the direct/iterated base-change cancellation identity.
- In `comparisonLocalIso_isIndependent`, the comparisons at any two cover
  points are fppf-locally pinned. Both are inner-equivalent to the same
  direct pullback of `e`. The existing uniqueness theorem therefore makes
  them equal. The evaluation identity transfers that equality to the
  local all-test maps; surjectivity of `testPointsEquiv` includes every
  input point on the original relative test.

The statement retains arbitrary, possibly nonaffine or nonreduced, relative
tests. It does not construct a pinned representative of an inner class.
That local existence input, and hence the unconditional
`RelativePinnedComparisonExistenceStatement`, remains separate.
