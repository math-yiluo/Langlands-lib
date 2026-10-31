# Naturality of the canonical Lie base-change comparison

This module states naturality in actual abelian-scheme homomorphisms for
comparison isomorphisms characterized by the exact equations of
`Langlands.AbelianScheme.LieBaseChangeStatement`. All declarations are
Prop-valued definitions. The module supplies no proof of naturality and
does not reprove existence of the Lie base-change isomorphism.

## All homomorphisms and the canonical equations

For arbitrary `S : Scheme.{u}`,
`Langlands.AbelianScheme.LieBaseChangeNaturalityStatement S` quantifies,
in order, `T : Scheme.{u}`, `b : T ⟶ S`, abelian schemes `A,B` over `S`,
an actual homomorphism `f : A ⟶ B`, and isomorphisms

```text
ellA : (pullback b).obj A.Lie ≅ ((AbelianScheme.baseChange b).obj A).Lie
ellB : (pullback b).obj B.Lie ≅ ((AbelianScheme.baseChange b).obj B).Lie.
```

The universe `u` is arbitrary, and both schemes lie in that common universe.
Write `A_T,B_T` for the actual base changes, `C_A,C_B` for their original
cotangent modules at the identity, and
`c_A = GroupScheme.cotangentBaseChangeMap b A.toGrp`, with analogous
notation for `B`. These are the published morphisms
`b* C_A ⟶ C_(A_T)` and `b* C_B ⟶ C_(B_T)`.

After the displayed telescope the proposition assumes, in order,
`IsIso c_A`, `IsIso c_B`, and the two canonical equations

```text
ellA.hom ≫ dualMap c_A = dualPullbackComparison b C_A
ellB.hom ≫ dualMap c_B = dualPullbackComparison b C_B.
```

These are exactly the characterizations in `LieBaseChangeStatement`;
the cotangent modules are written there as
`GroupScheme.cotangentAtIdentity A.toGrp` and similarly for `B`.
Since `A.Lie = dual C_A`, the first equation is an equality from
`b* A.Lie` to `dual (b* C_A)`, and similarly for `B`.
The isomorphisms and these characterizations are explicit quantified
inputs, so the naturality proposition can be used independently of a
chosen existence proof. The desired naturality is only a conclusion.

That conclusion is the square

```text
(pullback b).map (AbelianScheme.lieMap f) ≫ ellB.hom =
  ellA.hom ≫ AbelianScheme.lieMap ((AbelianScheme.baseChange b).map f).
```

The first path is `b* A.Lie ⟶ b* B.Lie ⟶ B_T.Lie`; the second is
`b* A.Lie ⟶ A_T.Lie ⟶ B_T.Lie`. Thus both paths are actual morphisms
of module sheaves on `T`. The abelian `lieMap` is the dual of the
cotangent map of the existing underlying group-scheme homomorphism.

## Endomorphisms and actual order actions

`LieBaseChangeEndomorphismNaturalityStatement S` quantifies `T,b,A`,
an actual `f : AbelianScheme.End A`, and a single comparison `ell`.
It assumes `IsIso c_A` and the single canonical equation for `ell`,
then equates
`(pullback b).map (lieMap f) ≫ ell.hom` with
`ell.hom ≫ lieMap ((baseChange b).map f)`.
It is the specialization `B = A`, `ellB = ellA = ell` of the preceding
all-homomorphism statement.

For any actual order action `α : O →+* AbelianScheme.End A`, this square
applies to `f = α a` for each `a : O`. Its right-hand endomorphism is the
Lie differential of the actual pulled-back endomorphism
`(AbelianScheme.baseChange b).map (α a)`, as used by the published
`baseChangeOrderAction` and `lieOrderAction_baseChange` in
`LieOrderBaseChange`. This explains the transport use without replacing
the all-homomorphism target by an action-specific assertion. The present
module does not assert a determinant identity.

`LieBaseChangeNaturalityStatements S` is the conjunction of the
all-homomorphism and endomorphism propositions, in that order, providing
one exact proof target.

## Existing laws and remaining proof

`Langlands.Scheme.Modules.dualMap` is already contravariantly functorial:
`dualMap_id` and `dualMap_comp` are proved in `ModuleDual.lean`.
The actual comparison also already satisfies
`dualPullbackComparison_naturality` in `ModuleDualPullback.lean`.
For a module morphism `a : M ⟶ N` it states

```text
(pullback b).map (dualMap a) ≫ dualPullbackComparison b M =
  dualPullbackComparison b N ≫ dualMap ((pullback b).map a).
```

The remaining proof content is naturality of the actual cotangent
base-change map in `CotangentBaseChangeNaturalityStatement`, followed by
dualization and cancellation. More precisely, let `k` be the cotangent
map of `f` and `k_T` its base change. The cotangent square gives
`b* k ≫ c_A = c_B ≫ k_T`; its dual and contravariant composition give
`dualMap k_T ≫ dualMap c_B = dualMap c_A ≫ dualMap (b* k)`.
Postcomposing the desired Lie square with `dualMap c_B`, substituting
the two canonical equations, and using the existing dual-pullback
naturality identifies both composites. Invertibility of `c_B` makes
its dual invertible, allowing cancellation. Both cotangent `IsIso`
hypotheses are retained in the statement to match the canonical
comparison setting requested here.

These are internal derived coherence statements for the cited Library
constructions and laws; no additional theorem is attributed to original
literature. No affine, reducedness, characteristic, flatness or
surjectivity hypothesis is imposed on the base schemes or their
morphism. Worker 274's separate Lie base-change existence proof is
reused through its published characterization and is outside this
statement group's proof obligations.

Worker 208 authored these statements and their explanation.
