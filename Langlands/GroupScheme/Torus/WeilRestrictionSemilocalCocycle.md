# Cocycle vanishing through Weil-restriction presentations

Let `A` and `B` be commutative rings in the same arbitrary universe, with
`B` a finite projective `A`-algebra. Let `G` be an actual group scheme over
`Spec A`, and supply an isomorphism
`e : G ≅ WeilGm.groupScheme A B`. The cover `U → Spec A` is affine, flat,
and surjective. The cocycle is the published all-test `Cocycle G U`.

When the module Picard group of `B` is subsingleton,
`weilPresentationPicardCochain` maps the cocycle through `e.hom`, takes the
published WeilGm Picard coboundary, and composes that point with `e.inv`.
Its specification proves the original cocycle equation
`ξ(a,b) = (a ≫ f) * (b ≫ f)⁻¹` on every test over `Spec A`.
The proof composes the published coboundary identity with `e.inv` and uses
multiplicativity, preservation of inverse, and `e.hom_inv_id`.
`isTrivial_of_weilPresentation_of_pic_trivial` packages this point and law
as triviality on the original cover.

`isTrivial_of_weilPresentation_of_finiteAlgebrasHaveTrivialPicard`
obtains the coefficient-ring Picard hypothesis from the published predicate
that all module-finite algebras over `A` have trivial Picard group.
`isTrivial_of_weilPresentation_of_semilocal` obtains that predicate from
finiteness of `MaximalSpectrum A`. Finally, `isTrivial_weil_of_semilocal`
applies the same result with the identity presentation of WeilGm.
Local finite presentation of the cover and faithful flatness or étaleness
of `B/A` are not needed. The finite-projective assumption already implies
flatness of `B/A`.

These are internal consequences of the published WeilGm Picard coboundary
and finite-algebra Picard results. The presentation is supplied, not
constructed from reductivity or from a lattice condition. No assertion is
made that every torus has such a presentation, and no quasi-split
inner-form theorem is proved here.
