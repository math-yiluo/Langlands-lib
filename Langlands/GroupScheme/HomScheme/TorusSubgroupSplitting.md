# Étale-local splitting of closed torus subgroups

Module `Langlands.GroupScheme.HomScheme.TorusSubgroupSplitting`. The auxiliary declarations are
in namespace `Langlands.GroupScheme.HomScheme.TorusSplitting`. The main theorem is
`Langlands.GroupScheme.HomScheme.exists_etale_splitPoints`.

## Statement and provenance

Let `G` be an affine group scheme over `Spec R` and `T` an affine scheme over `Spec R`. Let
`i : L ⟶ G_T` be a closed subgroup (`IsClosedSubgroup i`) such that `L` is a relative torus
(`RelativeTorus.IsTorus L`: it becomes a split torus on some étale cover of `T.left`).
`exists_etale_splitPoints` provides the following data:

- a natural number `n`;
- for each `k : Fin n`, a commutative `R`-algebra `C k` and a morphism
  `b k : specOver R (C k) ⟶ T` over `Spec R`;
- for each `k`, a finite type `I k` with decidable equality;
- for each `k`, a Hopf point `f k : AffineCoordinates.hopfAlgebra G →ₐ[R] C k ⊗[R] R[I k → ℤ]`.

These satisfy:

1. each `(b k).left` is étale;
2. the `b k` are jointly surjective onto `T.left`;
3. each `C k`-linear extension `AlgHom.liftEquiv R (C k) _ _ (f k).1` is surjective;
4. for each `k`, the evaluation `TorusSubgroupModuli.evaluate i (b k)` of the subgroup family `i`
   on the chart `b k` is the range of the split-torus homomorphism
   `(SplitTorusPoint.splitPointEquiv G (C k)).symm (f k)`.

By `isClosedSubgroup_splitPointEquiv_symm_iff`, condition 3 says that this split-torus
homomorphism is a closed immersion.

The statement was specified by Worker 1421, the first executor of the task "Prove smooth moduli of
actual closed torus subgroups" (torus case of SGA 3, Exp. XI, 4.1), as an input to the chart
construction there. It is a standard reduction, internal to this project. Étale-local splitting
of tori is the definition of `RelativeTorus.IsTorus`. Quasi-compactness of the affine scheme `T`
reduces the splitting cover to finitely many affine charts. On each chart the subgroup is
transported to Hopf points with the published bridge `SplitTorusPoint.splitPointEquiv`.

## Charts (`namespace TorusSplitting`)

Fix `T : Over (Spec R)`.

- `ChartRing A g` is a type synonym for the ring `A`, attached to a morphism
  `g : Spec A ⟶ T.left`. It carries the `R`-algebra structure given by
  `Spec.preimage (g ≫ T.hom)`, i.e. through `Spec A ⟶ T ⟶ Spec R`. The synonym keeps this
  `g`-dependent algebra structure off `A` itself.
- `chartHom A g : specOver R (ChartRing A g) ⟶ T` is `g` as a morphism over `Spec R`
  (`Over.homMk`, with compatibility `Spec.map_preimage`). `chartHom_left` says its underlying
  morphism is `g`.
- `chartRelHom G i A g I e`: here `e : (baseChange g).obj L ≅ splitTorus (Spec A) I` splits `L`
  over the chart. The result is the relative homomorphism
  `RelativeHom (splitTorus (Spec R) I) G (specOver R (ChartRing A g))`. It is the composite of
  the base-change identification `splitTorus.baseChangeIso`, `e.symm`, and the evaluated family
  `TorusSubgroupModuli.familyHom i (chartHom A g)`.
- `isClosedSubgroup_chartRelHom`: if `i` is a closed subgroup, then so is `chartRelHom`, by
  `IsClosedSubgroup.iso_comp` and `TorusSubgroupModuli.isClosedSubgroup_familyHom`.
- `evaluate_chartHom`: `TorusSubgroupModuli.evaluate i (chartHom A g)` is the range of
  `chartRelHom`, because precomposition with an isomorphism does not change ranges
  (`SubgroupFunctor.range_iso_comp`).

## Proof of `exists_etale_splitPoints`

Let `𝒰` be an étale cover of `T.left` over whose members `L` splits. Fix a point `t`, and let
`j t := 𝒰.idx t` and `y t` be a preimage of `t` in `𝒰.X (j t)`. Choose the member `a t` of the
Mathlib affine open cover of `𝒰.X (j t)` that contains `y t`. The chart is
`g t : Spec (A t) ⟶ 𝒰.X (j t) ⟶ T.left`. It is étale, as an open immersion followed by an étale
map, and its range contains `t`.

`L` splits over `g t`. Apply `IsSplitTorus.baseChange` to the splitting over `𝒰.f (j t)` and
transport along `baseChangeCompIso`. Choose `I t`, finite, and a splitting isomorphism `e t`.

The ranges of the `g t` are open, since étale morphisms are open maps. They cover the compact
space `T.left`, because `T.left` is affine. So finitely many of them, indexed by a finset `s`,
already cover it. Reindex `s` by `Fin s.card` with `Finset.equivFin`. For each chart, set
`C k := ChartRing (A t) (g t)`, `b k := chartHom`, `I k := I t` (with `Fintype.ofFinite` and
classical decidable equality), and `f k := splitPointEquiv G (C k) (chartRelHom …)`. Then:

- the étale condition is the étaleness of `g t`;
- joint surjectivity is the finite subcover;
- surjectivity of the linear extension comes from `isClosedSubgroup_splitPointEquiv_symm_iff`
  and `isClosedSubgroup_chartRelHom`;
- the range identity is `evaluate_chartHom`.
