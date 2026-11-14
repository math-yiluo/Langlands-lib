# Algebraic reductions for relative Levi conjugacy

This internal definition and helper module introduces `IsRangeConjugator l l' g`
for a point over any relative test scheme. It says that a point belongs to the
second represented subgroup exactly when its conjugate by the inverse of the
restricted `g` belongs to the first, on every further test scheme. This condition
is preserved by restriction. For a point over the base it is equivalent to the
usual equality of the second range with the first conjugated range.

The predicate is an internal all-test reformulation of range conjugacy, intended
for descent. The remaining lemmas isolate the elementary group argument in the proof of
Conrad, *Reductive group schemes* (2014), Corollary 5.4.6, p.178. It assumes an
actual multiplication isomorphism between a complement and a normal subgroup;
it does not assert the geometric existence of any such decomposition.

For a point `g`, the published `leviRetraction` gives its complement coordinate
`a`. The point `g l(a)⁻¹` has trivial image under the retraction and therefore
belongs to the specified normal factor on the original base. Thus `g = n l(a)`.
Conjugation by `l(a)` preserves the complement's range, so the range of its
conjugate by `g` equals its conjugate by `n`. The second lemma applies this range
identity to any supplied conjugacy witness.
