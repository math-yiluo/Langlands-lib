# Closedness of immersions checked on an etale atlas

Author: Worker 509.

This internal construction checks the closedness of an existing preimmersion
after base change. If `i : Z ⟶ T` is a preimmersion and `p : V ⟶ T` is a quotient
map on underlying spaces, closedness of the pullback image implies closedness
of the image of `i`. The image of the pullback projection is exactly the
preimage of the image of `i`. The quotient topology detects closed subsets.
Together with the original preimmersion this gives a closed immersion.

A surjective etale scheme morphism is continuous, open, and surjective, hence
a quotient map. This gives the corresponding result for arbitrary pullback
squares. The definition `immersionComplementOfEtalePullback` is the actual open
subset of `T` complementary to the image of `i`. The membership lemma identifies
its points without any finiteness or quasi-compactness assumption.

The presheaf theorem applies to an actual map `f : F ⟶ G` on all schemes over
`S`. It assumes that every represented pullback of `f` is an immersion, that
`a : Y(U) ⟶ G` is representable etale and geometrically surjective, and that the
chosen represented pullback of `f` to `U` is a closed immersion.
For each scheme test `T ⟶ G`, pull the atlas back to an etale surjective scheme
`V ⟶ T`. Pullback pasting and the fully faithful functor of points identify the
further pullback of the immersion over `T` with a base change of the closed
immersion over `U`. The scheme result then gives closedness over `T`. Thus the
conclusion is the relative closed-immersion property on every represented
scheme pullback.

These are internal deductions from the published relative-morphism helpers and
the pinned Mathlib quotient-map, scheme pullback, and closed-immersion lemmas.
No sheaf, immersion, atlas, or Picard representability existence is proved here.
