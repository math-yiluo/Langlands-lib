# Radical descent and pseudo-reductive ascent over Galois extensions

For an arbitrary Galois extension `K/k` and an affine group scheme `G` over
`k`, `IsUnipotentRadical.galoisRadicalDescent` constructs the actual descended
radical of a supplied represented radical of `G_K`. Its output contains a
group scheme over `k`, its radical inclusion into `G`, a source isomorphism
after scalar extension, and the equality recovering the specified inclusion.
There is no finite-degree or characteristic restriction.

The construction uses the global-section algebra of `G` and the canonical
affine presentation `affineSchemeOverIso`. The radical tensor-ideal and
ideal-sheaf adapters prove that its full defining ideal descends and therefore
that its two images on the double overlap agree. Effective closed-subgroup
descent, followed by reflection of the radical properties, gives the output
of `descentOfOverlapRangeEq`. No affine presentation, coefficient-invariance
condition or ideal-descent conclusion remains as a premise of this result.

`IsPseudoReductive.baseChange_galois` constructs a represented radical of
the base change using the published radical-existence proof. It descends
that radical by the preceding construction. Ground-field triviality makes
the descended radical's image trivial; base change and the recovering source
isomorphism make the original radical's image trivial. The greatestness
property of that radical yields the intrinsic trivial-radical predicate
for `G_K`. Smoothness and affineness follow from pullback, and connectedness
uses `connectedSpace_baseChange_of_smooth_affine`.

These are internal consequences of the imported constructions. The source
and inclusion are actual group schemes, and subgroup-functor equalities retain
all relative test schemes, including nonreduced tests. Worker 1359 authored
the assembly and the reused scheme ideal-descent adapters; Worker 1370
authored the tensor-coordinate and Galois ideal-descent proofs.
