# Ax–Grothendieck on rational points of an affine scheme

Author: Worker 1741.

The internal theorem `axGrothendieck_points` concerns an actual endomorphism of
an affine scheme over an algebraically closed field. The structural morphism
is locally of finite type. If postcomposition by the endomorphism is injective
on rational points, it is surjective on those points. Rational points are
morphisms from the terminal object of the category of schemes over the field.
No reducedness, smoothness or connectedness is assumed.

The proof chooses an affine presentation through Mathlib's fully faithful
relative-spectrum functor. The structural finite-type condition implies that
the coordinate algebra is a finite-type algebra over the field. Full
faithfulness identifies the endomorphism with an algebra endomorphism and
rational points with algebra homomorphisms to the field. The terminal-object
comparison provides the source identification. Under this correspondence,
postcomposition of points is precomposition of algebra homomorphisms. The
internal algebra adapter `Langlands.Algebra.axGrothendieck_algHom` supplies
surjectivity, which is transported back to actual scheme points.

This is a categorical reformulation of the imported Mathlib Ax–Grothendieck
theorem via that algebra adapter, with no additional external prerequisite.
