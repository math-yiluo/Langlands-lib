# Conjugating subgroup functors by a point on a test scheme

This internal construction expresses subgroup conjugacy by an actual group
point on an arbitrary test scheme. `SubgroupFunctor.IsConjugatingPoint F F' g`
requires, on every refinement of that test scheme, that a point belongs to `F`
if and only if its conjugate by the restriction of `g` belongs to `F'`.
The definition concerns all test schemes, rather than only geometric points.

Restriction preserves the relation, inversion reverses it, and successive
conjugations compose with the actual multiplication order. A point conjugates
a subgroup functor to itself precisely when it belongs to the published full
normalizer functor. Consequently two conjugating points differ on the right by
a normalizer point, and right multiplication by such a point preserves the
relation.

The fpqc descent theorem assumes that membership in both subgroup functors
descends along fpqc covers of test schemes. It pulls the supplied cover back
along each test morphism, uses the conjugacy relation there, and descends
membership in either subgroup. In particular, represented subgroup functors
of monomorphisms satisfy the membership hypotheses by the published
`hasFpqcMembershipDescent_range` theorem. Arbitrary scheme base change
preserves the relation when the pulled-back point corresponds to a refinement
of the original point under `baseChangePointsEquiv`.

These are derived consequences of elementary noncommutative group identities
and the existing subgroup-functor and fpqc membership APIs. No existence of
conjugating points or of a representing transporter is asserted.
