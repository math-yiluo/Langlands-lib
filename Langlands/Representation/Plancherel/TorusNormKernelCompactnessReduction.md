# Torus norm-kernel compactness from central norm-kernel compactness

Author: Worker 723.

This internal module reduces the published
`Plancherel.TorusNormKernelCompactnessStatement.{u}` to the published
`BruhatTits.RationalPoints.CentralNormKernelCompactnessStatement.{u}`. The second one
is the target of task `158e8cf8`: for every connected reductive `M` over a
nonarchimedean local field, `schemeCenterPoints M ⊓ rationalCommonNormKernel M` is
compact. The reduction applies that statement to a torus, which is commutative and
equals its own centre. The module proves neither statement outright. Following the
Library convention for conditional reductions, the final step is a proposition-valued
`def` under `set_option linter.defProp false`. The two supporting results are
unconditional theorems.

## `GroupScheme.IsTorus.isConnectedReductive`

Let `k` be a field and `T` a group scheme over `Spec k` with `IsAffineHom T.X.hom` and
`IsTorus T`. Then `IsConnectedReductive T`. The four fields are supplied as follows:

- smoothness by the published `IsTorus.smooth`;
- affineness by the hypothesis;
- connectedness of `T.X.left` by the published `IsTorus.connectedSpace`;
- a trivial unipotent radical after base change to `AlgebraicClosure k`. By the proved
  `torusFiniteGaloisSplitting`, `T` splits over a finite Galois extension `K/k`. Since
  `K/k` is algebraic, `IsAlgClosed.lift` embeds it into `AlgebraicClosure k` over `k`.
  `IsSplitTorus.baseChange_fieldTower` then splits `T` over the algebraic closure, and
  the published `IsSplitTorus.hasTrivialUnipotentRadical` applies to that split torus.

The affineness hypothesis is kept because `IsTorus` alone does not record it. Only the
torus property and affineness are used.

## `GroupScheme.schemeCenterPoints_eq_top_of_isCommMonObj`

If the underlying group object of `T` is commutative (`IsCommMonObj T.X`), then
`schemeCenterPoints T = ⊤`. A rational point `g` lies in the scheme centre when, for
every test `T'` over `Spec k`, every morphism of tests `a : T' ⟶ Over.mk (𝟙 _)` and every
`T'`-point `h`, the restricted point `a ≫ g` commutes with `h`. In a commutative Hom
group every pair of points commutes.

## `Plancherel.torusNormKernelCompactness_of_centralNormKernelCompactness`

Given `CentralNormKernelCompactnessStatement.{u}`, for a nonarchimedean local field `F`
and a torus `T` with `IsAffineHom T.X.hom` and `LocallyOfFiniteType T.X.hom`:

1. `T` is connected reductive by the first theorem, so the input gives compactness of
   `schemeCenterPoints T ⊓ rationalCommonNormKernel T` in `rationalPointTopology F T.X`.
   That is exactly the topology installed by `TorusNormKernelCompactnessStatement`.
2. `T` is commutative by the published `IsTorus.isCommMonObj`. Hence the centre is the
   whole point group by the second theorem, and the intersection is
   `rationalCommonNormKernel T` itself.

The local-finite-type hypothesis of the torus statement is not used.

## Provenance

The mathematical content is the remark that the central compactness statement
specializes to tori. Renard 2026 makes the same specialization implicitly: in V.2.6,
compactness of `⁰G ∩ Z(G)` for reductive `G` includes `G = T`. Source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, V.2.6 Proposition
(printed p.108 / PDF p.114). The structure of the reduction is internal.
