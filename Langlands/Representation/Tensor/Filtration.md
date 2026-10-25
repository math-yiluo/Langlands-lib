# Binary tensor image filtrations and their graded equivalences

Author: Worker 439.

This internal construction tensors a supplied finite filtration of an actual
representation over a field. The coefficient field `k`, monoid `G`, filtered
representation `A : Rep.{uA} k G`, and other factor `B : Rep.{uB} k G` have
independent coefficient, monoid, and carrier universes. Tensor carriers have
universe `max uA uB`. The construction uses Mathlib's tensor product and
`Representation.tprod` with its diagonal action.

For `s : ObjectRepFiltration A n`, `s.tensorRight B` is an actual
`ObjectRepFiltration (Rep.of (Representation.tprod A.ρ B.ρ)) n`.
The constructor `s.tensorLeft B` instead filters
`Rep.of (Representation.tprod B.ρ A.ρ)`. In this notation `B` is the fixed
left factor and `s` filters the right factor. For every `i : Fin n`,
`tensorRightGradedEquiv` and `tensorLeftGradedEquiv` give actual
equivariant linear equivalences

```text
(s.tensorRight B).gradedRepresentation i  ≃  (s.gradedRepresentation i) ⊗ B
(s.tensorLeft B).gradedRepresentation i   ≃  B ⊗ (s.gradedRepresentation i).
```

Here each displayed graded object carries precisely the actual quotient action
from `ObjectRepFiltration.gradedRepresentation`.

## Actual right image steps

The helpers in `Langlands.TensorFiltration` start with `inclusion S`, the
actual intertwining map from an invariant subspace `S` into `A`.
`tensorInclusion B S` is its right tensor with the identity of `B`, and
`tensorImage B S` is the range subrepresentation of this map. Its underlying
submodule is exactly
`LinearMap.range (S.toSubmodule.subtype.rTensor B)`, as recorded by
`tensorImage_toSubmodule`. Membership is existence of an actual tensor
preimage, by `mem_tensorImage`.

`tensorInclusion_injective` uses flatness of vector spaces over a field.
Restricting the codomain to the range gives `tensorImageMap`; its equivariance
is the original intertwining equation after taking subtype values.
Injectivity and range surjectivity produce `tensorImageEquiv B S` from
`S ⊗ B` to its actual image. `tensorImageEquiv_val` identifies its underlying
ambient vector with the canonical inclusion.

For `S ≤ T`, `stepInclusion` is the actual inclusion between the subspaces.
`tensorInclusion_stepInclusion` proves that tensoring this inclusion and then
including into `A ⊗ B` equals the tensorized inclusion of `S`. Consequently
`tensorImage_mono` proves monotonicity of the image construction.
`tensorImage_bot` follows because the zero subspace's inclusion is the zero
linear map. `tensorImage_top` follows from surjectivity of the full-subspace
inclusion and preservation of surjectivity by right tensoring.

`ObjectRepFiltration.tensorRight` applies these laws to the steps of `s`
using `ofSubrepresentations`. The law `tensorRight_subrepresentation` states
that every new step is exactly `tensorImage B (s.subrepresentation i)`.
Monotonicity and the zero/full endpoints are proved inside the constructor.

## Right graded quotient and representative law

For nested invariant subspaces `S ≤ T`, write `lower S T` for
`S.toSubmodule.comap T.toSubmodule.subtype` and `quotientRep S T` for the
representation on `T.toSubmodule ⧸ lower S T`. These are the published helpers
in `LengthCriterionProof`, and are definitionally the denominator and action
used by a consecutive graded object of `s`.

`quotientProjection S T` is the genuine quotient projection with this action.
`step_exact` proves exactness of the inclusion of `S` followed by this
projection by identifying its range and kernel on representatives.
`tensorInclusion_mem_image_iff` identifies the pullback of the lower tensor
image along the upper tensor inclusion with the range of the tensorized
inclusion from `S` to `T`. Its reverse and forward directions use the
factorization of inclusions and injectivity of the upper tensor inclusion.

`tensorQuotientMap B S T` first inverts `tensorImageEquiv B T`, then applies
the right tensor of the quotient projection. `tensorQuotientMap_kernel`
applies Mathlib's `rTensor_exact` to `step_exact` and the surjectivity of the
quotient projection. Its kernel is exactly the lower image pulled back to
the upper image. `tensorQuotientMap_surjective` follows from tensor
surjectivity and the upper image equivalence.

`quotientTensorMap` descends this map through `Submodule.liftQ` on the
existing quotient of actual image steps. Equivariance reduces to the
intertwining equation on quotient representatives.
`quotientTensorMap_bijective` proves injectivity using
`Submodule.ker_liftQ_eq_bot` and surjectivity using the preceding surjection.
`quotientTensorEquiv` packages it as an actual `Representation.Equiv`.

`quotientTensorEquiv_mk` evaluates this equivalence on the class of the image
of any tensor. Its pure tensor specialization
`quotientTensorEquiv_mk_tmul` sends the class of the image of `x ⊗ b` to
`[x] ⊗ b`. Applying this construction to consecutive steps defines
`ObjectRepFiltration.tensorRightGradedEquiv`.
`tensorRightGradedEquiv_projection_tmul` states the same representative law
using the actual `gradedProjection` maps of the original and new filtrations.

## Actual left images and graded quotients

`leftTensorInclusion B S` tensors `inclusion S` on the left with the identity
of `B`; `leftTensorImage B S` is its range subrepresentation.
`leftTensorImage_toSubmodule` and `mem_leftTensorImage` identify the
underlying range and its representatives. `leftTensorInclusion_comm`
proves on pure tensors that the ambient commutor intertwines this inclusion
with the right tensor inclusion.

`map_tensorImage_comm` then identifies the image of `tensorImage B S`
under the actual ambient commutor with `leftTensorImage B S`. This is an
equality of invariant subspaces. `leftTensorImage_mono`,
`leftTensorImage_bot`, and `leftTensorImage_top` transfer the corresponding
right image laws along the published subrepresentation order isomorphism.

`commImageEquiv` is the ambient commutor restricted to the right tensor image
and its transported image; `commImageEquiv_val` records the ambient vector.
`commQuotientEquiv_mk` records the representative formula for the published
`JordanHolderTransportProof.quotientEquiv` applied to these images.

`ObjectRepFiltration.tensorLeft` transports the right image steps along the
actual commutor using `subrepOrderIso`. Its step law
`tensorLeft_subrepresentation` proves that each step is the actual
`leftTensorImage`, and therefore the range of the canonical left inclusion.
`tensorLeftStepEquiv` identifies `B ⊗ sᵢ` with this actual step;
`tensorLeftStepEquiv_tmul_val` sends `b ⊗ x` to the ambient vector
`b ⊗ (x : A)`.

`tensorLeftGradedEquiv` composes the inverse of the published quotient
transport equivalence, the right graded equivalence, and the graded tensor
commutor. `tensorLeftGradedEquiv_projection_tmul` proves the representative
formula `[image(b ⊗ x)] ↦ b ⊗ [x]` using quotient transport cancellation and
the right representative law.

## Provenance and scope

This is internal algebra derived from the published actual filtration and
quotient definitions, the invariant-subspace and quotient transport helpers
in `JordanHolderTransportProof`, and Mathlib's tensor-product exactness and
flatness APIs. It is not a transcription of an external theorem. The Lean
proof route is the range/kernel calculation and actual quotient descent
described above; it chooses no composition factors or tensor functor axioms.

The only coefficient and monoid assumptions are `[Field k]` and `[Monoid G]`.
All carriers may be infinite-dimensional. Repeated steps and zero graded
pieces are retained. Zero representations and `n = 0` require no special
construction; when a length-zero filtration is supplied, its existing
endpoint laws force the ambient representation to be zero. There are no
irreducibility, smoothness, admissibility, finite-length, or nonzero
hypotheses. This pair constructs tensor filtrations and graded equivalences;
it asserts no Jordan–Hölder matching or p-adic external tensor theorem.
