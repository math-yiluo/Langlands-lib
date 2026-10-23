# Compatibility targets for the canonical pullback tensor comparison

This module states three laws for the fixed natural transformation
`pullbackTensorComparison` from the published `PullbackTensor` module.
Every statement is a proposition definition in arbitrary universe `u`.
No law is proved or assumed as an instance in this module.

For a scheme morphism `f : X ⟶ Y`, write `F_f` for
`AlgebraicGeometry.Scheme.Modules.pullback f` and `δ_f(M,N)` for
`pullbackTensorComparisonApp f M N`. Its direction is
`F_f(tensorObj M N) ⟶ tensorObj (F_f M) (F_f N)`.
All tensors and swaps below are the explicit sheafified sectionwise
constructions in `Tensor`, independently of a monoidal category instance
on module sheaves.

## Identity and composition

`PullbackTensorIdentityStatement` quantifies over every scheme `X` and
`M,N : X.Modules`. Applying `δ_(id X)` and then tensoring the two
components of the existing `Scheme.Modules.pullbackId X` is required to
equal its component on `tensorObj M N`.

`PullbackTensorCompositionStatement` quantifies over schemes `X,Y,Z`,
morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, and `M,N : Z.Modules`.
The existing comparison `Scheme.Modules.pullbackComp f g` has direction
`F_g ⋙ F_f ≅ F_(f ≫ g)`. Both sides of the stated equation start at
`F_f(F_g(tensorObj M N))` and end at
`tensorObj (F_(f ≫ g) M) (F_(f ≫ g) N)`. One path applies the composite
pullback comparison and then `δ_(f ≫ g)`. The other applies `F_f` to
`δ_g`, then `δ_f`, then the tensor of the two composite pullback
comparisons. The law therefore uses the existing canonical
`pullbackComp`, not a freely chosen isomorphism.

## Symmetry

`PullbackTensorSymmetryStatement` quantifies over every `f : X ⟶ Y` and
`M,N : Y.Modules`. Applying `δ_f(M,N)` and then `tensorComm` on the
pulled-back factors is required to equal pulling back `tensorComm M N`
and then applying `δ_f(N,M)`. This expresses preservation of the fixed
explicit factor swap.

`PullbackTensorCompatibilityStatement` is the conjunction of identity,
composition, and symmetry compatibility, in that order.

## Provenance and remaining obligations

Worker 59 authored these internal categorical targets. Their equations
are the tensor components of compatibility of an oplax monoidal functor
with identity/composition natural isomorphisms, and its compatibility
with symmetry, expressed directly using the published explicit tensor
and canonical maps. The relevant conventions are those of pinned
Mathlib's `CategoryTheory.Monoidal.Functor`,
`CategoryTheory.Monoidal.NaturalTransformation`, and
`AlgebraicGeometry.Modules.Sheaf`. The imported `Tensor` and
`PullbackTensor` Markdown record the sheaf-theoretic provenance of the
underlying constructions. These targets are internal specialization of
categorical laws, not claimed translations of a separate source theorem.

The statements have no flatness, quasicoherence, local-freeness,
affineness, invertibility, or coherence hypotheses. A separate proof
task must establish the conjunction without additional assumptions.
This unit does not assert tensor-comparison invertibility, associativity,
unit compatibility, or an assembled strong symmetric monoidal pullback
instance. The parent task also retains the comparison between the
explicit tensor's unitors and swap and the localized monoidal structure.
