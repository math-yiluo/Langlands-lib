# Explicit pullback tensor associativity

The theorem `Langlands.Scheme.Modules.explicitPullbackTensorAssociativity`
proves the existing `ExplicitPullbackTensorAssociativityStatement.{u}`.
It applies to arbitrary schemes `X`, `Y` in universe `u`, a morphism
`f : X ⟶ Y`, and module sheaves `M`, `N`, `P` on `Y`, without additional
hypotheses.

Write `F` for pullback along `f`, `T` for `tensorObj`, `c` for the fixed
`pullbackTensorComparisonApp f`, and `A` for the fixed `tensorAssociator`.
The theorem proves

```text
c(T(M,N),P) ≫ tensorMap(c(M,N),id(FP)) ≫ A(FM,FN,FP).hom
  = F.map(A(M,N,P).hom) ≫ c(M,T(N,P)) ≫ tensorMap(id(FM),c(N,P)).
```

Both composites go from `F(T(T(M,N),P))` to `T(FM,T(FN,FP))`.
The tensor is the explicit sheafified tensor. The imported statement, canonical
comparison, and transported associator are unchanged.

The private lemma `adjoint_tensor` identifies the adjoint of a canonical
pullback comparison followed by a tensor map. Naturality of the adjunction
hom correspondence, the published characterization of the canonical comparison,
and naturality of the pushforward tensor map express this adjoint as the
tensor of the two adjoints followed by `pushforwardTensorApp`.

The lemma `explicitPullbackTensorAssociativity_of_pushforward` transfers
`PushforwardTensorAssociativityStatement.{u}` to the pullback equation.
It applies the injective hom correspondence of the pullback–pushforward
adjunction to both composites and expands them using `adjoint_tensor`.
Functoriality of `tensorMap` factors out the tensor products of the adjunction
units. Pushforward associativity then identifies the remaining composites,
and naturality of the fixed associator at those units completes the equality.
The calculation uses a finite theorem-local heartbeat bound.

Finally, `explicitPullbackTensorAssociativity` supplies the independently
proved `pushforwardTensorAssociativity` from
`PushforwardTensorAssociativityProofs` to the transfer lemma. Thus the final
theorem has no associativity hypothesis and assumes no monoidal pullback
structure, comparison invertibility, or geometric restriction. The naturality
lemma imported from `Picard.RigidifiedTensorAssociativity` is unconditional;
its downstream results that assume pullback associativity are not used.
The localized tensor equation and its conjunction with this equation are
separate targets.

This is an internal categorical proof of the published statement. Worker 367
authored the transfer and final theorem. Worker 339 is a coauthor through the
adapted private `adjoint_tensor` calculation from the published
`PullbackTensorCompatibilityProofs`. The proof imports Worker 464's published
pushforward associativity theorem. It adds no axioms or proof holes.
