# Faithfully flat projections to actual closed affine orbits

This internal derivation first proves rational-point lifting for a surjective
morphism between schemes locally of finite type over an algebraically closed
field. The inverse image of the closed point of a rational section is a nonempty
closed subset of the Jacobson source. A closed point in that subset supplies the
rational lift, and rational-point extensionality verifies its composite.

For a quasi-compact scheme morphism with closed range, the underlying support of
its kernel is the closure of its range. The canonical factorization through the
schematic image is therefore surjective.

Apply these facts to an action of a reduced flat finite-type group over an
algebraically closed field on an affine locally finite type scheme. If the orbit
map of a rational point is quasi-compact and has closed range, its projection
to the actual schematic image is flat, surjective and quasi-compact. Indeed the
image is reduced, the restricted action has this exact orbit projection, and
rational-point lifting makes it transitive on rational points. The published
orbit-map faithful-flatness theorem then applies. Orbit closedness is an explicit
premise. Worker 362 authored this derivation from existing Library constructions.

When the acting group is smooth and affine and the orbit map has the exact
all-test right-coset fibers of a given smooth closed subgroup, the actual
schematic orbit image itself is the homogeneous quotient. The construction
`SchemeAction.quotientOfClosedAffineOrbit` returns the existing
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient` bundle with this image
as its scheme and the image projection as its projection. It has separated
finite-type geometry, a smooth surjective quasi-compact projection, and the
same exact coset fibers on every relative scheme test. Its underlying scheme
is affine, as stated by `quotientOfClosedAffineOrbit_affine`.

To prove smoothness of the image projection, first use the published homogeneous
quotient construction for the supplied exact-fiber ambient map. Its smooth
projection and the flat surjective quasi-compact image projection are effective
epimorphisms with identical all-test fibers. The published quotient-comparison
construction gives a compatible isomorphism between their targets. Composing the
smooth projection with this isomorphism proves smoothness of the image projection.
The affine, separated and finite-type properties follow from its closed inclusion
in the original affine scheme. This comparison avoids any additional claim about
monomorphisms into the ambient scheme.

This result does not prove the closed-orbit premise, and it does not descend a
quotient from an algebraically closed field to an arbitrary field. It is a
supporting construction for the host ordered-product task, whose final target
remains separate.
