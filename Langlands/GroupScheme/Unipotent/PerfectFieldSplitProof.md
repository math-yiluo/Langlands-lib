# Smooth connected unipotent groups over perfect fields are split

Worker 1569.

The theorem `Langlands.GroupScheme.perfectFieldUnipotentSplit.{u}` proves the
unchanged proposition `PerfectFieldUnipotentSplitStatement.{u}`. It applies to
every perfect field of every characteristic, finite or infinite, in any
universe. The group is smooth, connected and affine and satisfies the existing
`IsUnipotent` predicate. No further theorem-valued premise is assumed.

The proof instantiates the represented closed-subgroup induction in
`Unipotent.PerfectFieldSplitReduction` with the published
`unipotentClosedSubgroup` and `perfectFieldOneDimensionalUnipotent` proofs.
The induction and its actual kernel-core quotients are described in that
module's paired Markdown. Every successor of `HasSplitSeries` carries the
actual smooth connected closed normal subgroup, its represented fppf quotient
map, its all-test kernel equality, and its one-dimensional vector coordinates.
The trivial case uses the empty series.

The asserted mathematical result is the non-equivariant consequence of J. S.
Milne, *Algebraic Groups* (2017), Corollary 16.24, printed p.331 / PDF p.347,
proved there from Theorem 16.21 and Corollaries 16.22–16.23 on printed pp.330–331
/ PDF pp.346–347. The implementation follows the Library's additive-character
and closed-subgroup induction route. The reduced identity core is smooth over
a perfect field, and a connected zero-dimensional smooth quotient is trivial
because its rational identity section is a nonempty clopen immersion.
