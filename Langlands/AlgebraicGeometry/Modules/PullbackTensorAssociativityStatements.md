# Pullback tensor associativity statements

This module specifies associativity for the fixed canonical pullback tensor
comparison in the two published tensor conventions. Both propositions
quantify over all schemes `X,Y : Scheme.{u}`, all morphisms `f : X ⟶ Y`,
and all module sheaves `M,N,P : Y.Modules`, in an arbitrary universe `u`.
They have no additional hypotheses.

Write `F` for the existing `Scheme.Modules.pullback f`.
The symbol `⊗` denotes the published localized monoidal tensor on the actual
scheme-module sheaf category. Write `T(M,N)` for the explicit sheafified
tensor `tensorObj M N`, and `t(a,b)` for its map `tensorMap a b`.
These tensor objects are related by the fixed natural isomorphism
`localizedTensorIso`, from `M ⊗ N` to `T(M,N)`.

## Localized tensor

Write `d(M,N)` for `localizedPullbackTensorComparisonApp f M N`,
with direction `F(M ⊗ N) ⟶ FM ⊗ FN`, and `α` for the associator of the
published monoidal structure. The proposition
`LocalizedPullbackTensorAssociativityStatement` is the equation

```text
d(M ⊗ N,P) ≫ (d(M,N) ▷ FP) ≫ α(FM,FN,FP).hom
  = F.map α(M,N,P).hom ≫ d(M,N ⊗ P) ≫ (FM ◁ d(N,P)).
```

Both paths start at `F((M ⊗ N) ⊗ P)` and end at
`FM ⊗ (FN ⊗ FP)`. Here `▷` and `◁` are the morphism whiskerings
of the localized monoidal category. The equation specializes the
`CategoryTheory.Functor.OplaxMonoidal.oplax_associativity` field to
the fixed comparison. It does not assume an oplax monoidal instance.

## Explicit sheafified tensor

Write `D(M,N)` for `pullbackTensorComparisonApp f M N`, with direction
`F(T(M,N)) ⟶ T(FM,FN)`, and `A(M,N,P)` for the fixed
`tensorAssociator M N P` from `TensorCoherenceMaps`. The proposition
`ExplicitPullbackTensorAssociativityStatement` is the equation

```text
D(T(M,N),P) ≫ t(D(M,N),𝟙 FP) ≫ A(FM,FN,FP).hom
  = F.map A(M,N,P).hom ≫ D(M,T(N,P)) ≫ t(𝟙 FM,D(N,P)).
```

Both paths start at `F(T(T(M,N),P))` and end at `T(FM,T(FN,FP))`.
The associator `A` is the published transport of the localized associator
through `localizedTensorIso`. The localized comparison `d` is the
published conjugate of `D` by this same natural tensor isomorphism.
All maps are fixed constructions, not parameters satisfying assumed laws.

## Combined target and provenance

`PullbackTensorAssociativityStatement` is exactly the conjunction of
the localized and explicit propositions in the same universe.
Worker 59 authored these internal categorical specifications. Their
provenance is the fixed constructions imported from `TensorCoherenceMaps`
and the associativity convention in pinned Mathlib's
`CategoryTheory/Monoidal/Functor.lean`, class `Functor.OplaxMonoidal`.
The inherited sheaf-theoretic construction and its original sources are
documented in the imported modules. This unit is not a translation of a
separate literature theorem.

This module introduces three Prop-valued definitions and proves none of
them. A focused proof task must establish the exact combined target.
The parent task also retains tensor-comparison invertibility, the unitor,
symmetry, identity and composition compatibility laws, comparison of
localized and explicit unitors and symmetry, and the assembly of strong
symmetric monoidal pullback.
