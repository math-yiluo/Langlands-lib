# Points whose commutators are central

`Langlands.GroupScheme.SecondCenterTrivial G` says, for a group scheme `G` over a
scheme `S`: whenever `g : T ⟶ G.X` is a point over a test scheme `T` such that,
for every morphism `a : T' ⟶ T` of test schemes and every point `h : T' ⟶ G.X`,
the commutator `(a ≫ g) * h * (a ≫ g)⁻¹ * h⁻¹` lies in the scheme-theoretic
centre `center G` over `T'`, then `g` itself lies in `center G` over `T`.

In words, the second term of the upper central series of the group functor of
`G` coincides with its first term (the centre). The commutator is written out
explicitly rather than with Mathlib's scoped `⁅·,·⁆` notation; it is the point
`g h g⁻¹ h⁻¹` of the group `T' ⟶ G.X` (Mathlib's `Hom.group`).

Provenance: this is an internal interface definition for the proof that the
quotient of a connected reductive group by its full centre has trivial centre
(Milne, *Algebraic Groups* (2017), Corollary 17.62(e)). That proof has two
halves: a formal fppf-descent half (lift a central point of the quotient
locally to a point of `G` whose commutators all lie in the kernel, the centre
of `G`) and a group-theoretic half (such a point is central). The definition
names the property passed between the two halves; it makes no claim about any
particular group.
