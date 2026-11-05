# Unipotent radicals with invariant overlap images

This internal deduction combines the published effective descent of affine closed
subgroups with reflection of the full represented unipotent-radical predicate.
It works for arbitrary fields in a common universe and uses the existing actual
group schemes, pullbacks and all-test subgroup functors without modification.

`UnipotentRadicalDescent i` bundles a group scheme over the ground field, its
radical inclusion, an actual source isomorphism after scalar extension, and
the equality recovering the specified inclusion `i`. It adds no assumptions
to the existing radical predicate. The noncomputable constructor
`IsUnipotentRadical.descentOfOverlapRangeEq` chooses this data from the
effective existence theorem below.

For an affine group `G` over `k`, a field extension `K/k`, and a represented
radical `i : U ⟶ G_K`,
`IsUnipotentRadical.exists_descent_of_overlap_range_eq` assumes equality of the
two subgroup images on the actual double overlap. Effective affine closed
subgroup descent constructs `U₀`, its closed inclusion `j : U₀ ⟶ G`, and an
actual isomorphism `(U₀)_K ≅ U` recovering the inclusion. Transport of the
radical through that source isomorphism, followed by the published
`IsUnipotentRadical.of_baseChange`, proves the full radical predicate for `j`.
Thus the overlap equality remains an explicit input; no Galois invariance to
overlap invariance comparison is asserted here.

`SubgroupFunctor.range_eq_bot_of_radical_descent` pulls back the trivial image of a
descended radical and removes its source isomorphism. Together with greatestness
of the radical over `K`, this gives
`HasTrivialUnipotentRadical.baseChange_of_radical_overlap_range_eq`.

`IsPseudoReductive.baseChange_finiteGalois` has no radical or descent premise.
For a finite Galois extension it constructs a radical over `K` using the
published radical-existence theorem, descends it by
`IsUnipotentRadical.finiteGaloisRadical`, and applies the preceding triviality
argument. Smoothness and affineness are preserved by pullback; connectedness is
preserved by the published geometric connectedness theorem for smooth connected
affine group schemes. This proves the full pseudo-reductive predicate after
finite Galois extension. Preservation under infinite separable extension and
the perfect-field comparison remain separate obligations.

The provenance is internal: these are deductions from the unchanged published
`Descent.ClosedSubgroups`, `Rational.UnipotentRadicalProperties`,
`Reductive.UnipotentRadicalExistenceProof`, and geometric connectedness APIs.
