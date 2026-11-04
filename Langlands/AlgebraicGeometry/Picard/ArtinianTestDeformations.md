# Actual pointed Picard deformations on Artinian tests

This is an internal specialization of `PicardGroupoid.PointedTestDeformations`.
It restricts that construction along the actual spectrum functor of augmented
local Artinian algebras from `Deformation.ArtinianTests`. No existence theorem
for deformations or charts is used.

Fix a commutative base ring \(k\), a field \(K\) with its given
\(k\)-algebra structure, a scheme \(X\) over \(\operatorname{Spec} k\),
and an actual line bundle \(M\) on the relative fibre over
\(\operatorname{Spec} K\). For an augmented test \(A\), `Deformations f M A`
is the groupoid of actual line bundles on the chosen relative fibre product
over \(\operatorname{Spec} A\), with a specified isomorphism from \(M\)
to their restriction along \(\operatorname{Spec} K\to\operatorname{Spec} A\).
The chosen fibre products and the orientation of the reduction isomorphism
are those in `PointedTestDeformations`. Objects are not isomorphism classes.

`mk` constructs such an object from its bundle and its specified reduction.
`reductionIso` exposes that actual reduction isomorphism. Morphisms are
the same compatible bundle isomorphisms as in the general pointed-test
construction; the inherited category is a groupoid.

For an augmentation-preserving algebra map \(q:A\to B\), `restrict f M q`
is a functor from the deformation groupoid at \(A\) to the one at \(B\).
This is covariant in algebra maps because spectrum and geometric
pullback each reverse arrows. `restrict_obj_bundle` and `restrict_map_iso`
identify the underlying bundle and arrow operations with ordinary relative
pullback along \(\operatorname{Spec} B\to\operatorname{Spec} A\).
`restrict_obj_reductionIso` identifies the new specified reduction with
the old one followed by the original pullback-composition comparison.

`pseudofunctor` packages these groupoids and operations on the full
category of augmented Artinian tests. It composes the opposite-valued
spectrum functor with the existing pointed-deformation pseudofunctor,
using Mathlib's pseudofunctor composition. Its identity, composition and
coherence data are inherited through that composition, rather than
assumed from the caller. The two final formulas identify its objects
and arrow functors with the constructions displayed above.

All types have arbitrary universe \(u\). No properness, flatness, finite
presentation, splitting of the augmentation, or algebra structure of
\(K\) on \(A\) is required. This module does not prove infinitesimal gluing,
formal versality, existence of a hull, effectivity, algebraization,
openness of versality, or existence of a smooth atlas.
