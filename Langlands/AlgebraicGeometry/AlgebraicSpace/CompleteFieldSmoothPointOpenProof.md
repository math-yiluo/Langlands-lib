# Smooth maps of algebraic spaces are open on points over complete fields

Author: Worker 3519.

`completeFieldSmoothSpacePointOpen` proves `CompleteFieldSmoothSpacePointOpenStatement`
(`CompleteFieldSmoothPointOpenStatement.lean`). Let `K` be a complete nontrivially normed field,
archimedean or not, of any characteristic. Let `X` and `Y` be separated algebraic spaces locally of
finite type over `Spec K` and `f : X ⟶ Y` a morphism with `IsSmoothMorphism f`. Then
`RingPoints.map f : X(K) → Y(K)` is an open map for the étale-chart topologies
`etaleChartTopology K X` and `etaleChartTopology K Y`. The proof uses no representability,
surjectivity or fibre condition on `f`. It also uses no estimate over finite fields.

## Source

This is the local step of Conrad's Theorem 5.9. Source: Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The relevant passages are:

- printed p.11, smooth maps of schemes are open on points over complete fields;
- printed p.15, the étale-chart topology and the lifting of rational points to étale charts;
- printed p.17, the remark that the proof of Theorem 5.9 carries the scheme argument over to
  algebraic spaces.

Conrad does not state this algebraic-space assertion separately. The proof below is the
chart-by-chart argument that the p.17 remark asks for.

## Implemented proof

The existing `HenselianFinitePointProperProof.isQuasiSeparated_of_isSeparated` shows that a
separated space is quasi-separated, because a closed immersion is quasi-compact. Separatedness
of `X` and `Y` is used only through this lemma.

For the main theorem, let `N ⊆ X(K)` be open and `x ∈ N`. The proof finds an open set
containing `f x` inside `f(N)`, as follows.

1. A complete nontrivially normed field is henselian (`completeHenselianValuedField`).
2. The published `exists_chart_pointMap_eq` (Knutson II.6.4, through
   `rationalPointEtaleLiftStatement`) gives a finite-type étale chart `c` of `X` with a rational
   point `u` over `x`. It also gives a chart `d` of `Y` with a rational point `v` over `f x`.
3. Let `a = c ≫ f : h_U → Y` and `b = d : h_V → Y`. The scheme `W = pairPullback a b`
   represents `U ×_Y V`. Its first projection `W → U` is étale (`etale_pairPullbackFst`), so `W`
   is locally of finite type over `K`. The composite `h_W → h_U → X` is étale (`isEtale_map`,
   `IsEtale.comp`), and the square of `h_W → X`, `h_V → Y` and `W → V` commutes. By
   `IsSmoothMorphism.smooth_chart` (smoothness holds on every commuting étale chart square),
   the projection `W → V` is a smooth morphism of schemes.
4. The points `u` and `v` have the same image `f x` in `Y(K)`. By `exists_pairPullback_point`
   they come from a rational point `w` of `W`.
5. Three point maps are used.
   - `ψ : W(K) → X(K)`, `w' ↦ c(w' ≫ pr₁)`, is continuous. It is the scheme map
     `W(K) → U(K)` (`schemePointContinuity_proof`) followed by the chart map
     (`EtaleFiniteTypeChart.continuous_pointMap`).
   - `φ : W(K) → V(K)`, `w' ↦ w' ≫ pr₂`, is open by the scheme theorem
     `completeFieldSmoothPointOpen`.
   - The chart map `d : V(K) → Y(K)` is open over the henselian field `K`
     (`EtaleFiniteTypeChart.isOpenMap_pointMap`).
6. The set `d(φ(ψ⁻¹(N)))` is open and contains `d(v) = f x`, because `w ∈ ψ⁻¹(N)`. For
   `w' ∈ ψ⁻¹(N)`, `schemePointsMap_pairPullbackFst` gives `d(φ(w')) = f(ψ(w'))`, so
   `d(φ(w')) ∈ f(N)`. Hence `f(N)` is open.

## Scope

The theorem keeps every quantifier of the statement: the universe `u`, every complete nontrivially
normed field, and separated spaces locally of finite type. It assumes only `IsSmoothMorphism f`.
The axioms used are `propext`, `Classical.choice` and `Quot.sound`.
