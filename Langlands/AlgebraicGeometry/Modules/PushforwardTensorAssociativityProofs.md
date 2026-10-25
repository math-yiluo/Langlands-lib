# Associativity of the canonical pushforward tensor map

Worker 464 proves
`Langlands.Scheme.Modules.pushforwardTensorAssociativity` with exact type
`Langlands.Scheme.Modules.PushforwardTensorAssociativityStatement.{u}`.
The theorem quantifies over all schemes `X,Y : Scheme.{u}`, every morphism
`f : X ⟶ Y`, and all `M,N,P : X.Modules`, with no additional hypotheses.

Write `G = Scheme.Modules.pushforward f`, `T = tensorObj`, `t = tensorMap`,
`c(M,N) = pushforwardTensorApp f M N`, and `A = tensorAssociator`.
The proved equality is

```text
t(c(M,N),id GP) ≫ c(T(M,N),P) ≫ G.map A(M,N,P).hom
  = A(GM,GN,GP).hom ≫ t(id GM,c(N,P)) ≫ c(M,T(N,P)).
```

The source is `T(T(GM,GN),GP)` and the target is `G(T(M,T(N,P)))`.
The proof uses the existing definitions of both `c` and `A` unchanged.

## The fixed associator and the sheafification unit

For a scheme `X`, let `S = sheafify X`, let `U` be the forgetful functor from
module sheaves to module presheaves, and let `e(M,N) = tensorSheafifyUnit M N`.
The published `TensorMonoidal` module proves that `S` is strong monoidal.
Mathlib's `Adjunction.rightAdjointLaxMonoidal`, applied to `sheafifyAdjunction X`,
therefore supplies a lax monoidal structure on `U`. The file installs this
proved structure only as the explicitly named local instance
`pushforwardAssociativityForgetLax`.

Let `d(M,N) = localizedTensorIso X M N`, whose direction is
`M ⊗ N ≅ T(M,N)`. The private lemma `forgetTensorComparison` identifies the
induced forgetful tensor comparison `μ` by definitional equality:

```text
μ(M,N) = e(M,N) ≫ U.map d(M,N).inv.
```

Cancelling the comparison isomorphism gives
`e(M,N) = μ(M,N) ≫ U.map d(M,N).hom`. Unfolding the fixed definition of `A`
gives `localizedTensorIso_associativity`. Naturality and associativity of the
derived lax comparison `μ` then prove `tensorSheafifyUnit_associator`:

```text
(e(M,N) ⊗ id) ≫ e(T(M,N),P) ≫ U.map A(M,N,P).hom
  = α_presheaf.hom ≫ (id ⊗ e(N,P)) ≫ e(M,T(N,P)).
```

Thus the implemented argument proves the action of the fixed associator on
nested pure tensors; it does not assume that action or choose a new associator.

## Why triples of pure tensors suffice

The private lemma `tensorTriple_hom_ext` proves that maps from `T(T(M,N),P)`
are determined after precomposition on underlying presheaves by
`(e(M,N) ⊗ id) ≫ e(T(M,N),P)`.

The forgetful functor `U` is fully faithful. Consequently the sheafification
adjunction makes `S.map e(M,N)` invertible. Strong monoidality of `S` then
makes `S.map (e(M,N) ⊗ id)` invertible. The proof cancels this latter map
and uses naturality and injectivity of the sheafification hom equivalence.
It does not assert that the presheaf sheafification unit is an epimorphism.

## The pushforward calculation

Apply this extensionality lemma on `Y` to the two target composites.
Naturality of `e` moves each `tensorMap` through the outer unit. The existing
`tensorHomEquiv_pushforwardTensorApp` identifies `e(GM,GN) ≫ c(M,N).val`
with the canonical `pushforwardTensorPresheafHom f M N`.
The associator formula above rewrites the right-hand composite.

Presheaf morphism extensionality and
`ModuleCat.MonoidalCategory.tensor_ext₃'` reduce the equality to a triple of
sections `m,n,p` on an inverse-image open `f⁻¹U`.
By the published definitions, the pushforward presheaf comparisons send each
pure tensor to its image under `e` on this open. Both sides are therefore
exactly `tensorSheafifyUnit_associator M N P` evaluated on `(m ⊗ n) ⊗ p`.
The last step is this evaluation by `congrArg` and definitional reduction.
A finite recursion-depth bound of 4000 is scoped to the final theorem to
elaborate these nested section expressions.

## Provenance and scope

This is an internal proof of the published statement, authored by Worker 464.
Its mathematical inputs are the existing `Tensor`, `PullbackTensor`,
`TensorMonoidal`, and `TensorCoherenceMaps` constructions, imported through
the statement module, together with Mathlib's monoidal-adjunction coherence
and module tensor extensionality. It introduces no new literature assertion.
All helper lemmas and the auxiliary lax instance are private or local.

The theorem assumes no monoidal structure on pullback or pushforward, no
invertibility of their canonical tensor comparisons, and no geometric
restriction. It does not import the pullback associativity or compatibility
proof modules. The subsequent adjunction transfer to the explicit pullback
equation and its localized version remain the respective consumer tasks.
