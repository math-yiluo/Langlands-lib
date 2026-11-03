# Smooth connected pointed-image generation targets

These are honest proposition targets, with one proved conditional adapter,
for the source construction in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), paragraph preceding Proposition 3.3.5, printed p.109
(PDF p.135), in the split-torus setting introduced on printed p.107; registered
source `conrad-gabber-prasad-2015-pseudo-reductive`.

The source starts with a geometrically integral closed subscheme through the
identity and describes stabilization of finite-product images, citing Borel
2.2, followed by the closed-subsemigroup-to-subgroup argument citing EGA IV₄
17.9.6. The present formulation is derived: it accepts any actual pointed
morphism from a geometrically integral finite-type affine scheme. The passage
to its geometrically integral image and the correspondence with the fixed
closed envelope are part of the proof obligation. No separability, perfectness,
characteristic-zero restriction, or smoothness of an image closure is assumed.
The cited Borel and EGA inputs are literature obligations, not axioms.

`GeneratedImage.HasSmoothConnectedGeneration D` asserts that the actual
representing group is smooth, affine and geometrically connected over the
base and that `D.powerMap n` is dominant for some strictly positive natural
number `n`. Dominance is `IsDominant` of the actual underlying scheme
morphism. The power map is ordered multiplication of the actual factor
`D.factor`, so its composite with the actual inclusion agrees with the
ordered product map into the ambient group on every test scheme.

`PointedImageGenerationStatement` quantifies over every field in universe
`u`, a smooth affine actual group scheme, an affine geometrically integral
source whose structure morphism is locally of finite type, a rational point
of that source and an actual morphism carrying the point to the identity.
Affineness implies quasi-compactness, so the stated source is of finite type.
It asserts existence of `D : GeneratedImage f` with the preceding geometric
properties. The data of `D` already require an actual closed immersion
representing the intersection of all closed subgroup functors containing the
image. Its proved laws give the unique actual source factor and unique
minimal group-scheme homomorphism into every competing closed subgroup,
including competitors that are not smooth or reduced.

`PointedImageEnvelopeStabilityStatement` imposes the same geometric source
hypotheses and an actual split torus, a scheme action on the source, an
automorphic action on the ambient group, and all-test equivariance of `f`.
It asserts stability of the same fixed closed envelope under the ambient
action. It does not replace that envelope with a larger invariant closure.

`InvariantPointedImageGenerationStatement` asserts existence of the same
representative with geometric properties, an actual automorphic action on it,
stability of its envelope, equivariance of its inclusion and factor, and a
strictly positive dominant ordered product map equivariant for the actual
diagonal source action.
`invariantPointedImageGeneration_of_generation_and_stability` proves this
target conditionally on the two preceding targets: it uses the existing
represented-subgroup restriction for the action, cancels the actual inclusion
for factor equivariance, and applies the ordered-product equivariance law to
the positive power supplied by generation. It does not prove either geometric
premise.

`ImageGenerationSourceStatement` collects the remaining group-integrality,
pointed-generation and envelope-stability obligations. Each is intended for a
focused proof successor after publication. The special commutator weight bound
and semigroup realization are outside these targets and stay with their
existing consumer proof tasks.
