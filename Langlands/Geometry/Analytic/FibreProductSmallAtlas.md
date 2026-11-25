# Same-universe atlases from a small spectrum cover

This internal construction separates cardinal smallness from the local
analytic net construction. The field universe is independent of the common
space and index universe.

`AffinoidChartSystem.small_space_of_small_charts` assumes a small index type
and a pointwise cover of the actual full quotient by chart spectra that are
small in the desired universe. Select the indices with small spectra. The
sigma of their actual spectra is small and its original chart map surjects
onto the quotient. Thus the full quotient is small. The cover concerns each
actual quotient point, not just a pair of separately specified factor
points. No neighborhood or topology condition is needed for this cardinal
argument.

For a fibre-product chart system with original index universe `v`, suppose
its full quotient is `Small.{v}`. Then its `LocalAtlasIndex`, being a subtype
of the set of actual subsets of that quotient, is also `Small.{v}`.
`smallAtlas` transports the already proved local analytic atlas along the
canonical `Shrink.homeomorph`, then reindexes it along `equivShrink.symm`.
It retains the exact affinoid algebras and full bounded restrictions. Both
the new space and new index type lie in `Type v`.

`smallPresentation` packages that actual atlas in
`AffinoidAtlasPresentation.{u,v,v}`. `smallSpaceHomeomorph` identifies its
space with the full original quotient and retains every quotient point.
Saturation of the three original atlases and smallness of the full quotient
are explicit hypotheses. This module does not infer smallness from an etale
leg or construct the complete strong projections or localized universality.
Those are further requirements of `LocalizedEtalePullbackStatement`. No external statement is
transcribed.
