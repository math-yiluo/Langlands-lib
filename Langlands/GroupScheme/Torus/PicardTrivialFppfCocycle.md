# Picard-trivial torus cocycles on arbitrary single fppf covers

Let `A` and `B` be commutative rings in a common arbitrary universe.
Assume that `B` is a finite projective `A`-algebra and that an actual group
scheme `G` over `Spec A` is supplied with an isomorphism to
`WeilGm.groupScheme A B`. Let `U → Spec A` be flat, surjective and
locally of finite presentation. Its total space can be non-affine and
non-quasi-compact. Cocycles use the published natural all-test definition.

`isTrivial_of_weilPresentation_fppf_of_pic_trivial` proves original-cover
triviality when the module Picard group of `B` is subsingleton. It applies
the affine fppf reduction `isTrivial_of_affine_fppf` and supplies the
published Weil-presentation Picard vanishing on each affine cover.
`weilPresentationFppfPicardCochain` chooses the resulting morphism
`U → G`; its specification gives the coboundary equation for every
test scheme. `isTrivial_weil_fppf_of_pic_trivial` uses the identity
presentation for the canonical WeilGm group.

`isTrivial_of_weilPresentation_fppf_of_finiteAlgebrasHaveTrivialPicard`
gets the coefficient Picard hypothesis from triviality of Picard groups
of all finite `A`-algebras. The semilocal specialization
`isTrivial_of_weilPresentation_fppf_of_semilocal` obtains this predicate
from finiteness of `MaximalSpectrum A`.
`isTrivial_weil_fppf_of_semilocal` again uses the canonical presentation.
These results do not require that `B/A` be étale or faithfully flat.

For a finite index type `I` and a subsingleton module Picard group of
`A`, `isTrivial_split_fppf_of_pic_trivial` applies the same affine fppf
reduction to the published coordinatewise split-torus vanishing.
`splitFppfPicardCochain` chooses an original-cover cochain, and its
specification proves the all-test coboundary identity.

These are internal deductions from the affine fppf refinement, cocycle
reflection, split-torus Picard and Weil-presentation Picard results.
They extend the cover scope and retain the supplied finite-projective
WeilGm presentation. They do not construct such presentations from a torus
condition, or prove the reductive quasi-split inner-form target.
