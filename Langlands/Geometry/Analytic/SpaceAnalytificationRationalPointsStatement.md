# Rational points of analytifications of separated algebraic spaces

`SpaceAnalytificationRationalPointsStatement` says the following. Let `K` be a
complete ultrametric nontrivially normed field, `X` a separated algebraic space
over `Spec K` that is locally of finite type, and `(Y, p)` an analytification of
`X` in the sense of `IsAnalytification`. Then:
1. the underlying topological space `localizedSpaceFunctor.obj Y` of `Y` is
   Hausdorff;
2. for every finite polynomial presentation `P₀` of `K`, the map
   `rationalPoint p P₀ : RingPoints K X K → localizedSpaceFunctor.obj Y` is a
   topological embedding (injective and inducing). Here `X(K)` carries the
   Library's étale-chart topology `etaleChartTopology K X`.

This module states the proposition only; it supplies no proof.

## Statement

The statement quantifies over a universe `u` and:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- an algebraic space `X` over `Spec (CommRingCat.of K)` with `IsSeparated X` and
  `LocallyOfFiniteTypeOverBase X`;
- `Y : LocalizedCategory.{u, u, u}`, `p : PointFamily K X Y` and
  `IsAnalytification K X Y p`.

The conclusion is
`T2Space (localizedSpaceFunctor.obj Y) ∧ ∀ P₀,
@IsEmbedding _ _ (etaleChartTopology K X) _ (rationalPoint p P₀)`.

`rationalPoint p P₀ x` is the image, under the map attached to the `K`-point
`x`, of the analytic point of the identity `K`-point of `K`. The étale-chart
topology is the strongest topology on `X(K)` for which `U(K) → X(K)` is
continuous for every étale map `U → X` from a scheme of finite type over `K`.
Each `U(K)` carries the Library's scheme point topology. It is the topology of
Conrad's Proposition 5.4. The statement does not claim that the image of
`rationalPoint` is closed or that it is the set of all `K`-rational points of
`Y`.

## Provenance

The first source is Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Printed
p.19, proof of Proposition 5.11(3), gives `X(k) = Xᵃⁿ(k)` as sets by [CT, Ex.
2.3.2]. It also says that an admissible affinoid covering of `Xᵃⁿ` topologizes
`X(k)` compatibly with all the properties required for uniqueness in
Proposition 5.4, "since rigid-analytic étale maps are local isomorphisms near
rational points". So it recovers the topology of Proposition 5.4.

The second source is Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
- Example 2.3.2, printed pp.11–12: points of `X` and `Xᵃⁿ`; every point has a
  residually trivial étale scheme neighbourhood [Kn, II, 6.4].
- Theorem 4.2.2, printed p.20, and printed p.25: the `k`-analytic
  analytification of a separated `X` is separated.
- Printed p.2, after Remark 1.2.3, and printed pp.19–20, proof of Theorem 4.1.4:
  a separated `k`-analytic space has Hausdorff underlying space.

The formulation is derived. Conrad works with the rigid space `Xᵃⁿ` and its
`k`-points; this statement uses the subspace of the Berkovich space consisting
of the points attached to `K`-points. Through the affinoid domains of
Berkovich's space, the two give the same topology on `X(K)`.

## Why the statement should be true

Every analytification is isomorphic to Conrad–Temkin's `k`-analytic `Xᵃⁿ`,
which is separated and hence Hausdorff. For injectivity, let `x` and `x'` be
`K`-points with the same image. Choose étale affine neighbourhoods
`Spec A → X` and `Spec A' → X` with `K`-points `a` and `a'` over `x` and `x'`.
The pullback condition identifies `(Spec A ×_X Spec A')ᵃⁿ` with the fibre
product of the analytifications, so this fibre product has a point over the
analytic points of `a` and `a'`. Since `Spec A ×_X Spec A'` is closed in
`Spec A ×_K Spec A'`, it then has a `K`-point over `(a, a')`. Hence `x = x'`.

Continuity follows by testing on étale charts. For an affine chart, the map
`U(K) → Uᵃⁿ` is continuous for the scheme point topology, and the map
`Uᵃⁿ → Y` is continuous. For the embedding property, take an étale affine
neighbourhood `Spec A → X` of a `K`-point with a `K`-point `a` over it. The
étale map `Spec(A)ᵃⁿ → Y` is a local isomorphism near the rational point `a`.
So open neighbourhoods of `a` in `Spec(A)(K)` map to traces of open sets of
`Y`.
