# Schematic images of group homomorphisms over a field

This internal construction equips Mathlib's scheme-theoretic image of an
actual group-scheme homomorphism with a group law. It is intended to support
torus-image descent. It derives its content from the published schematic
dominance and closed-immersion lifting lemmas in `ImageGenerationAppend` and
`ImageGenerationDominant`, and the published restriction constructor in
`CategoryTheory/GroupObjectDescent`. It asserts no new literature translation.

Work over any field `k : Type u`, with group schemes `G` and `H` over
`Spec k` and a homomorphism `f : G ⟶ H`. The target structure morphism is
affine and the underlying morphism of `f` is quasi-compact. There is no
affineness, finite type, reducedness, smoothness, connectedness or
commutativity assumption on the source. The target need not be smooth.

`imageOver f` is the scheme-theoretic image of the underlying scheme
morphism, with its structure morphism to the original field.
`inclusionOver f` is the canonical closed immersion and `projectionOver f`
is the canonical factor. Their composite is the underlying morphism of
`f`. The image is affine over `k`; its projection is quasi-compact and
schematically dominant.

Every scheme over a field is flat. The published tensor dominance theorem
therefore makes the tensor square of the projection schematically dominant.
The homomorphism identity for multiplication shows that ambient
multiplication factors through the image after precomposition with this
tensor square. Closed-immersion lifting along schematic dominance then
gives `imageMul`. The same argument for inversion gives `imageInv`; the
source unit directly supplies `imageOne`.

Restricting the ambient group structure along the monomorphism
`inclusionOver` proves the group axioms. Both the inclusion and projection
preserve multiplication and the unit. The final definitions `image`,
`inclusion` and `projection` package the actual group scheme and its
factorization, with `projection_inclusion` recording the original
homomorphism. Instances retain the closed inclusion, affine image,
quasi-compact projection and schematic dominance.

This module does not prove that a torus has a torus image, or any maximal
torus base-change or parabolic classification statement. Those remain
separate obligations.
