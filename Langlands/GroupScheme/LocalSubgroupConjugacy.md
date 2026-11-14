# Local conjugacy from subgroup-valued differences

This internal bridge identifies the all-test
`SubgroupFunctor.IsConjugatingPoint` relation for represented subgroup functors
at a rational base point with equality of ranges after the actual inner
automorphism. The conjugation order is `g*x*g⁻¹`.

The relation is preserved and reflected by arbitrary base change. Reflection
regards every original refinement as a test scheme over the new base and
transports it by the identity scheme isomorphism. The final equivalence uses
`baseChangeBasePointsEquiv` to identify a point on any original test scheme
with an actual rational point of the pulled-back group. No flatness or
monomorphism hypothesis is needed for these equivalences.

`HasZariskiLocalSubgroupConjugacy i j` says that each base point has an open
neighbourhood on which an actual rational point conjugates the first
base-changed subgroup range onto the second. The theorem from local coset
representatives assumes monomorphic subgroup inclusions, a quasi-compact
faithfully flat cover, and a conjugating point on it. On each open supplied by
the coset factorization, right multiplication by the subgroup cochain preserves
conjugacy because subgroup points normalize the subgroup. The factorization
identifies this corrected point with the pullback of the local base section.
Fpqc descent of membership in both represented subgroups then gives the
conjugacy relation for that section. The range equivalence above gives the
required actual rational conjugator.

If the source subgroup is self-normalizing, the inverse-coboundary differences
of the supplied conjugating point lie in that subgroup: the difference of two
conjugators is in the source normalizer. Over any affine base `Spec R`, the final
theorem combines this observation with `LocalCosetDescent`: it assumes an
affine source subgroup with an fppf quotient onto a split torus and a
monomorphic kernel inclusion representing the actual quotient kernel, whose
group has a finite affine vector series. An affine faithfully flat conjugating
cover then gives Zariski-local conjugacy. No field, connectedness, or nonzero
ring hypothesis is imposed.

These are internal consequences of pointwise range membership, group
cancellation, the pullback-point equivalences, subgroup membership descent,
and the preceding local coset theorem. No cover, self-normalizing subgroup,
split-torus quotient, or vector series is constructed here. In particular,
the hypotheses needed to apply the final theorem to relative Borel subgroups
remain separate proof obligations.
