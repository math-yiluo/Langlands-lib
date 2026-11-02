# Scheme point fibres under fully faithful transformations

This internal comparison specializes
`PseudofunctorPointFiberTransport.presheafIso` to the full category of actual
schemes over a base. It uses the published `Stacks.SchemeAtlas` conditions and
introduces no geometric existence assumption.

Fix `S : Scheme.{u}`, category-valued pseudofunctors `F` and `G` on `Over S`
with fibre morphisms and objects in universe `u + 1`, and a strong transformation
`α : F → G`. Assume explicitly that the component functor of `α` at every
`Z : Over S` is fully faithful. For actual objects `ξ` over `U` and `η` over `T`,
`fullyFaithfulPointFiberIso` identifies their two full scheme point-fibre
presheaves, with the objects on the `G` side being the actual images under `α`.
The isomorphism is the generic point-fibre comparison precomposed with
`T.iteratedSliceBackward.op`, exactly as in the generic scheme-atlas definition.
It therefore retains every actual test scheme over `T.left` and every
restriction morphism, together with the base maps and actual isomorphisms in
those fibres.

`fullyFaithfulPointFiber_smoothSurjectiveRepresented_iff` transports a natural
representation by composing with this isomorphism in one direction and its
inverse in the other. It retains the same `P : Over T.left`, the same structure
morphism `P.hom`, and the same witnesses of smoothness and surjectivity.
Thus the comparison concerns scheme-represented fibres, including the full
universal property, rather than algebraic-space representation or agreement
on geometric points.

`isSmoothSurjectivePresentation_iff_on_fullyFaithful_image` quantifies this
comparison over all `T : Over S` and all actual source fibre objects `η`.
It says precisely that the presentation condition on `F` is equivalent to
smooth surjective scheme representations for the ambient `G` point fibres of
these image objects. It does not assert that every object of `G` is in the
image. The last lemma applies this equivalence to an ambient presentation when
its atlas object is the actual image of `ξ`; the stronger ambient presentation
hypothesis supplies every required image-object fibre as a special case.

Every declaration preserves the arbitrary universe `u`. Empty, nonreduced,
nonnoetherian and non-quasi-compact tests are unrestricted. The module neither
constructs the fully faithful transformation nor proves its geometric image
open. It constructs no atlas and gives no coherent-stack algebraicity or
Picard-stack existence theorem. These geometric inputs remain obligations of
the parent proof task.
