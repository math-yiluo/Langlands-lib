# The coroot criterion for simple connectedness (sufficiency)

This module proves the published proposition `SplitCorootSpanSimplyConnectedStatement`
(`Langlands.GroupScheme.SimplyConnected.SplitCriterionStatement`) without hypotheses. Its
theorem `splitCorootSpanSimplyConnected` has type
`SplitCorootSpanSimplyConnectedStatement.{u}` for an arbitrary universe `u`.

The statement says: let `G` be a semisimple group over a field `k`, `i : T ⟶ G` a maximal
torus with `T` split, and `P` a root datum of `i` whose coroots span the cocharacter
lattice (`P.corootSpan ℤ = ⊤`). Then `G` is simply connected, so every central isogeny
`H ⟶ G` from a semisimple group `H` is an isomorphism.

## Proof

The proof is one application of the published conditional reduction
`splitCorootSpanSimplyConnected_of_rootDatumHom`
(`Langlands.GroupScheme.SimplyConnected.SplitCriterionReduction`). Its arguments are
accepted Library proofs of its three premises:

* `RootDatumExistenceStatement` (`Langlands.GroupScheme.Reductive.RootDatumStatement`):
  proved by `rootDatumExistence` in `Langlands.GroupScheme.Reductive.RootDatumExistence`
  (task `972e4466-2aff-4fc0-a62e-1be346c899a0`);
* `CentralIsogenySplitMaximalTorusLiftStatement`
  (`Langlands.GroupScheme.CentralIsogeny.SplitTorusLiftStatement`): proved by
  `centralIsogenySplitMaximalTorusLift` in
  `Langlands.GroupScheme.CentralIsogeny.SplitMaximalTorusLiftProof` (task
  `aa3b37a9-010c-46d5-8cc8-cdc83c6a456b`);
* `CentralIsogenyRootDatumHomStatement`
  (`Langlands.GroupScheme.CentralIsogeny.SplitRootDatumStatement`): proved by
  `centralIsogenyRootDatumHom` in `Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof`
  (task `ce241772-26d6-47b2-9310-94e6c02d897a`).

The Markdown of `SplitCriterionReduction` describes the argument and how it relates to
Milne, *Algebraic Groups* (2017), Proposition 23.29 (printed p. 493) via Proposition 23.5
(printed pp. 485–486). In short:

1. Lift the split maximal torus through the central isogeny `H ⟶ G`.
2. Take a root datum of the lifted torus.
3. The isogeny gives a morphism of root data. Its weight and coweight maps are injective,
   and its weight map is bijective exactly when the isogeny is an isomorphism.
4. The coroot hypothesis makes the coweight map surjective, so it is bijective.
   Transposition then makes the weight map bijective.

## Independence from cover existence

The Markdown of `SplitCorootSpanSimplyConnectedStatement` requires that a proof not use
the existence of simply connected covers. This proof does not. The modules it imports
transitively include no cover-existence module (for example
`SimplyConnected.CoverExistenceStatement`). The only `SimplyConnected` modules among
them are `Basic`, `SplitCriterionStatement` and `SplitCriterionReduction`. The routes of
the three premise proofs, described in their own Markdown, are:

* existence of the root datum: Weyl-group rationality, the finite Weyl image and root
  reducedness;
* torus lift: the kernel exponent, fpqc power-map descent, the torus image and finite
  rigidity;
* morphism of root data: the root-datum morphism construction, with the kernel-containment
  premise from `maximalTorusCentralizer`.

## Scope

The module proves only the sufficiency half of the coroot criterion. It does not prove the
converse, the existence of simply connected covers, or the invariance of simple
connectedness under field extension. The target statement and every file it imports are
unchanged.
