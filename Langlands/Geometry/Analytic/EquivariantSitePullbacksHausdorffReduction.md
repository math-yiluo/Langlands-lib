# Equivariant quasi-étale fibre products from Hausdorff stability

The module proves
`Langlands.Analytic.SaturatedAtlasPresentation.equivariantQuasiEtalePullbacksHausdorffReduction`,
whose type is `EquivariantQuasiEtalePullbacksHausdorffReductionStatement.{u, v, z}`
(module `QuasiEtaleHausdorffStabilityStatement`): the Hausdorff composition,
base change and over-morphism statements of that module, for every complete
ultrametric normed field, imply `EquivariantQuasiEtalePullbacksStatement`.

## Proof

The proof is that of `equivariantQuasiEtalePullbacks_of_stability` (module
`EquivariantSitePullbacksReduction`), with each stability premise applied
together with the Hausdorff hypothesis it requires. Let `f₁ : U₁ ⟶ U₃` and
`f₂ : U₂ ⟶ U₃` be arrows of `Qét(X(G))`. Every object `U` of this category
has as underlying object a `G`-space, and the first component of its
property `gSpaceProperty` (module `ContinuousAnalyticAction`) is
`T2Space (localizedSpaceFunctor.obj (GSpace.forget.obj U.left))`.

1. The structure arrows of `U₁` and `U₃` are quasi-étale, and
   `forget f₁ ≫ U₃.hom = U₁.hom` by `MorphismProperty.Over.w`. The
   over-morphism statement, applied with the Hausdorff middle object `U₃`,
   shows that `forget f₁` is quasi-étale.
2. `exists_localizedPullback_of_quasiEtale` (module
   `LocalizedQuasiEtalePullbackExistence`) gives a pullback square
   `IsPullback p q (forget f₁) (forget f₂)` with vertex `P`.
3. The base change statement, applied to this square with the Hausdorff
   source `U₁` of `forget f₁`, shows that `q : P ⟶ U₂` is quasi-étale.
4. The first component of `hasCompactPairPreimages_of_quasiEtale` (module
   `LocalizedPullbackCompactPreimages`), with `U₁` and `U₂` Hausdorff, shows
   that the underlying space of `P` is Hausdorff.
5. The composition statement, applied to `q` and the structure arrow of `U₂`
   with the Hausdorff objects `P` and `U₂`, shows that the composite to `X` is
   quasi-étale. `exists_equivariantSitePullback_of_isPullback` (module
   `EquivariantSitePullbacksReduction`) then equips `P` with the diagonal
   action and produces the required object of `Qét(X(G))` and its two
   projections.

## What the conclusion rests on

The Library holds the three premises as follows:

- base change: proved, `quasiEtaleHausdorffBaseChange` (module
  `QuasiEtaleHausdorffBaseChangeProof`);
- morphisms over a common base: proved, `quasiEtaleHausdorffOverMorphism`
  (module `QuasiEtaleHausdorffOverMorphismProof`);
- composition: reduced to `EtaleDomainQuasiEtaleStatement` (module
  `QuasiEtaleCompPrerequisites`) by `quasiEtaleHausdorffCompReduction`
  (module `QuasiEtaleHausdorffCompReduction`).

`EtaleDomainQuasiEtaleStatement` says that an étale morphism into an
analytic domain, followed by the inclusion of the domain, is quasi-étale;
the Markdown of `QuasiEtaleCompPrerequisites` relates it to Berkovich 1993,
Theorem 3.4.1 and Corollary 3.4.2. Through this reduction,
`EquivariantQuasiEtalePullbacksStatement` therefore rests on the single
unproved proposition `EtaleDomainQuasiEtaleStatement`, for every complete
ultrametric normed field.

The Library also proves `EquivariantQuasiEtalePullbacksStatement` without
any premise: `equivariantQuasiEtalePullbacks` (module
`EquivariantQuasiEtalePullbacksProof`). That proof does not use the general
composition statement. For the composite `P → U₂ → X` it proves
quasi-étaleness directly (`quasiEtale_common_of_isPullback_over`), from local
domain–étale factorizations and compact quasi-étale diagonals.

## Scope

The theorem is a reduction: the three Hausdorff stability statements are its
premises and are not proved in this module, and it uses no other unproved
proposition.
