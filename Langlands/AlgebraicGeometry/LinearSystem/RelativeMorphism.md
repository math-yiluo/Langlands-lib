# Relative linear-system morphisms and pullback of generating sections

This module constructs the actual morphism from a scheme `X` over a scheme
`S` to `RelativeProjectiveSpace S n` determined by a line bundle `L` and
`n + 1` global sections with no common zero. All schemes lie in an arbitrary
fixed universe. No hypothesis on the base scheme, the dimension `n`, or the
structure morphism is imposed.

The construction specializes the existing commutative-ring linear-system map
to the lifted integers and then applies the published relative projective
space's pullback universal property. The integral structure map is the unique
map to `Spec (ULift Z)`. The two projection identities recover the given base
map and the integral linear-system map.

The full inverse image of each coordinate chart is the whole generation open
of its defining section. For the polynomial map, the forward implication is
tested at the residue-field point of each point of `X`, using the existing
field-point chart-recognition lemma. The reverse implication uses the existing
point-map chart-membership lemma at the same residue-field point. The relative
assertion follows by composing inverse images with the integral projection.

The map is compatible with arbitrary pullback of the line bundle and its
sections. The existing equality between pulled-back whole generation opens
and inverse-image generation opens proves that the pulled-back sections still
generate. For a ratio of pulled-back sections, the pullback-composition
isomorphism takes its defining scalar equation to the defining equation along
the composite morphism. Injectivity of this isomorphism on global sections and
uniqueness of the ratio prove equality of the ratios. The chart ring maps,
point maps, and glued polynomial maps then agree. Uniqueness of the integral
structure morphism gives the integral version. Finally the two projections
of relative projective space prove the relative version for any commutative
square of base and source maps; the square need not be Cartesian.

This is an internal consequence of the published constructions in
`LinearSystem/Morphism`, `LinearSystem/SectionRatio`,
`Modules/PullbackSectionOpenProof`, and `RelativeProjectiveSpace`, with the
coordinate-chart definition from `RelativeProjectiveSpace/TwistOne`.
The original geometric construction behind the polynomial map is Stacks
Project, Section 27.14, Lemma 27.14.1, tag 01NJ, in registered source
`stacks-very-ampleness-support-2026-10-29`. This module does not construct the
isomorphism between the pullback of the projective twist and `L`, projective
bundles of nontrivial locally free sheaves, or embeddings.
