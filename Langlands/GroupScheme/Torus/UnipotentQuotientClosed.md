# Closed torus images in quotients with unipotent kernel

This internal adapter constructs
`HomImage.sourceImageIsoOfMono`, the actual isomorphism from a smooth
connected affine source to the schematic image of a monomorphism. Its
torus specialization `IsUnipotent.torusQuotientImageIso` identifies a closed
source torus with the schematic image of its composite with a quotient map.
The specialized homomorphism is exactly `SchematicImage.projection (i ≫ q)`.

All fields in universe `u` are permitted, including finite and imperfect
fields, in every characteristic. The source torus need not split over
the field.

## General closedness argument

For a smooth connected affine source `A` and an affine target `G` locally
of finite type, the published `HomImage` construction factors a group
homomorphism `f` through its actual schematic image. The projection is
flat, surjective and quasi-compact. If the underlying morphism in the
over category is monic, its underlying scheme morphism is monic, and so
is the image projection. Mathlib's
`Flat.isIso_of_surjective_of_mono` makes that projection an isomorphism.
Reflection of isomorphisms by the forgetful functors gives the
group-scheme isomorphism `HomImage.sourceImageIsoOfMono`.

The published `HomImageEmbedding` module supplies
`HomImage.isClosedSubgroup_of_mono` with the same hypotheses, using
factorization through a closed image inclusion. The torus specialization
`IsTorus.isClosedSubgroup_of_mono` obtains smoothness and connectedness
from the published intrinsic geometry of tori; it retains an explicit
affine-source assumption.

## Quotient application

Let `N` be affine, locally of finite type and unipotent, let `G` and `Q`
be affine groups, with `Q` locally of finite type, and let
`i : T ⟶ G` be a closed torus. Let `n : N ⟶ G` be any homomorphism,
and suppose that the range of the full kernel of `q : G ⟶ Q` lies in
the range of `n`, on every relative scheme test.

The explicit premise `UnipotentClosedSubgroupStatement` permits the
existing `IsUnipotent.mono_torus_quotient` argument. Affineness of `T`
follows from the closed immersion `i` and affineness of `G`.
The general closedness result proves
`IsUnipotent.closed_torus_quotient`: `i ≫ q` is itself a closed
subgroup inclusion with the original torus as its source. The same
argument constructs `IsUnipotent.torusQuotientImageIso`, whose return type
retains the affine-source instance required to form the schematic image.
This instance follows from `hi` as above. The
companion homomorphism identity identifies it with the canonical
schematic-image projection.

No flatness, surjectivity, normality or quotient universal property of
`q` is assumed or proved. Full maximality of the image, sections, torus
lift existence and rational conjugacy remain separate obligations.
Closed-subgroup unipotence is still a hypothesis.

## Provenance

This is an internal consequence of the published schematic image,
smooth-connected image theorem and torus geometry, the conditional
unipotent-kernel monicity adapter, and Mathlib's faithfully flat
monomorphism criterion. It introduces no new literature statement
or mathematical axiom.
