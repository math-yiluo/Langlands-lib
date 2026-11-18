# Étale affine tests for algebraic-space morphisms

This internal reduction supports the proof of
`SpaceAnalytificationEtaleStatement`. Its open-cover construction generalizes the
published `CoproductChart.pullbackOpenCover` and
`CoproductChart.isEtale_of_forall_ι` from coproduct component covers to arbitrary
scheme open covers. The cover maps retain their actual structure maps to the
fixed base. Pullbacks in the over category are compared with scheme pullbacks
using preservation by the forgetful functor.

`SchemeOpenChart.isEtale_of_cover` represents every pullback using the target's
representable diagonal, pulls back the given open cover, pastes the resulting
squares, and invokes Mathlib's source Zariski locality of scheme étaleness.
No analytic property or unpublished comparison theorem is assumed here.

`isEtaleMorphism_iff_finiteTypeAffineTests` restricts the defining scheme tests
for `IsEtaleMorphism` to spectra of finite-type algebras over a nontrivially
normed field. Given an arbitrary étale scheme chart, its affine open cover
has locally finite-type structure maps by
`locallyOfFiniteType_of_isEtale`. The canonical isomorphism with the spectrum
of its global sections identifies each member with a finite-type algebra
test. Isomorphism invariance and the preceding open-cover lemma recover the
original test. Only the source space is assumed locally of finite type;
no separatedness or analytification hypothesis is used.
