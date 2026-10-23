# Rigidifying a specified tensor inverse

This module constructs the rigidification on a supplied inverse line bundle
from an actual tensor evaluation isomorphism. It proves that evaluation
respects the rigidifications and therefore gives an inverse equation in the
existing quotient by compatible isomorphisms.

## Source and scope

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI, paragraph
(6.2), printed p.88 (PDF p.92), defines a rigidification along
`ε : S ⟶ X` as an isomorphism `O_S ≅ ε*L`. A compatible morphism `h`
satisfies `α ≫ ε*(h) = β`. The paragraph defines multiplication of rigidified
classes by tensoring the two rigidifications through the canonical unit and
pullback–tensor identifications.

The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The construction below is an internal categorical derivation from that
convention and the published sheaf tensor, pullback, unitors and comparison.
It is not presented as a separate theorem quoted from the source.

The source's additional hypotheses on the structural morphism concern its
identification with the Picard sheaf and the absence of automorphisms. Neither
conclusion is asserted here. The construction works along any scheme morphism
`ε`, subject to the explicit published proposition
`pullbackTensorComparisonIsIsoStatement`. It requires a specified ordinary
line bundle `M` and a specified isomorphism `L ⊗ M ≅ O_X`.
Existence of an ordinary inverse, an inverse operation on all classes,
and the full group structure are not proved by this module.

## Construction

Write `F = ε*`, `A = F(L)`, `B = F(M)`, `α : O_S ≅ A`, and let
`e : L ⊗ M ≅ O_X` be the supplied evaluation. Write
`c : F(L ⊗ M) ≅ A ⊗ B` for the fixed pullback–tensor comparison and
`u : F(O_X) ≅ O_S` for the fixed pullback-unit isomorphism.

`RigidifiedModule.inverseTrivialization` constructs the actual isomorphism

`δ : B ≅ O_S`

by the sequence

`B → O_S ⊗ B → A ⊗ B → F(L ⊗ M) → F(O_X) → O_S`.

The maps are, respectively, the inverse left unitor, the tensor of `α`
with the identity, `c⁻¹`, the pullback of `e`, and `u`.
`RigidifiedModule.rigidifyInverse` equips `M` with `β = δ⁻¹`.
All these are maps between actual sheaves of modules.

## Compatibility proof

`tensorLeftUnitor_inv_naturality` follows from the published left-unitor
naturality by cancellation. `tensorRigidification_factor` combines it with
functoriality of the actual tensor map to show

`λ_O⁻¹ ≫ (α ⊗ β) = β ≫ λ_B⁻¹ ≫ (α ⊗ id_B)`.

The existing `tensorObj_rigidification_comp` identifies the rigidification
of `L ⊗ M` after composing with `c`. Cancelling this invertible comparison
and using the factorization above expresses that rigidification as
`δ⁻¹ ≫ λ_B⁻¹ ≫ (α ⊗ id_B) ≫ c⁻¹`.
After composing with `F(e)` and `u`, the expression is
`δ⁻¹ ≫ δ = id`. Thus `inverseEvaluation_compatibility` proves precisely
that the tensor rigidification followed by `F(e)` is `u⁻¹`, the
rigidification of the trivial bundle. No additional unitor or associator
coherence hypothesis is needed.

## Line bundles and classes

`RigidifiedLineBundle.rigidifyInverse` retains the supplied local rank-one
property of `M`. `inverseEvaluationIso` lifts the specified `e` to an
isomorphism from the rigidified tensor to `trivial ε`, using the proved
compatibility equation. `inverseEvaluationIso_forget` states that forgetting
rigidification recovers exactly `e`, by definitional equality.

For a morphism with a section and any test scheme `T`,
`classesTensor_rigidifyInverse` applies `Quotient.sound` to this compatible
isomorphism. It proves that the class of `L` tensored with the class of this
rigidified `M` equals the canonically rigidified trivial class.
The class relation retains compatibility with rigidification.
