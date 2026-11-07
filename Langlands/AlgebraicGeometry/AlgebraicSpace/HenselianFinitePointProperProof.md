# Finite maps of algebraic spaces are proper on rational points

Author: Worker 105.

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianFinitePointProperStatement.{u}`,
Corollary 5.12 of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.20. The entry theorem is `henselianFinitePointProper`.

The target: let `K : Type u` be a nontrivially normed field with `IsHenselianValuedField K`
that is algebraically closed in its completion (`algebraicClosure K K̂ = ⊥`). Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `Spec K` with `X`, `Y` separated
(`IsSeparated`) and locally of finite type over the base (`LocallyOfFiniteTypeOverBase`),
and `hom f` finite (`AlgebraicSpace.IsFinite`). Then `RingPoints.map f : X(K) → Y(K)` is a
proper map (`IsProperMap`) for `etaleChartTopology K X` and `etaleChartTopology K Y`.

## Route

Conrad first passes to the completion, using Proposition 5.11(2) and algebraic closedness to
see that the square of `K`- and `K̂`-points is cartesian. He then works locally on `Y` through
étale charts, reduces to `Y` affine and `X = Spec A[t]/(h)`, and uses continuity of roots.
The Lean proof skips the completion step: continuity of roots holds directly over `K`
(`HenselianRootContinuity.exists_tendsto_root`, which uses algebraic closedness in `K̂`).
It also argues with ultrafilters rather than reducing to `Spec A[t]/(h)`.

## Declarations

- `HenselianFinitePointProperProof.isQuasiSeparated_of_isSeparated`: a separated algebraic
  space is quasi-separated (closed immersions are quasi-compact;
  `MorphismProperty.relative_monotone`).
- `henselianFinitePointProper : HenselianFinitePointProperStatement.{u}`.

## Proof of `henselianFinitePointProper`

1. `X` and `Y` are quasi-separated, `Y` is locally separated
   (`isLocallySeparated_of_isSeparated`), and `Y(K)` is Hausdorff
   (`t2Space_etaleChartTopology`). The point map is continuous (`continuous_ringPointsMap`).
   By `isProperMap_iff_ultrafilter_of_t2` it remains to show the following. If `𝒰` is an
   ultrafilter on `X(K)` with `f(𝒰) → y`, then `𝒰` converges.
2. `RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement` gives an affine `V`, an étale
   `b : V → Y` and `v ∈ V(K)` over `y`. `V` is locally of finite type
   (`locallyOfFiniteType_of_isEtale`) and `b` is an étale morphism of spaces, so `b` is a local
   homeomorphism on points (`isLocalHomeomorph_ringPointsMap`). Let `e` be a partial
   homeomorphism through `v` agreeing with it. Its target is an open neighbourhood of `y`, so
   its preimage `W` under `f` belongs to `𝒰`.
3. Let `P = X ×_Y V` be the represented pullback of `hom f` along `hom b`, with
   `g : P ⟶ V` and `q : h_P ⟶ X.presheaf`. `g` is a finite morphism of schemes
   (`hf.property_snd`), so `P` is affine and locally of finite type over `K`. By
   `HenselianFinitePointProper.isProperMap_affineFinitePointMap` and
   `schemePointTopology_eq_affine`, `p ↦ p ≫ g` is proper on `K`-points.
4. For `x ∈ W` the points `x ∈ X(K)` and `e.symm (f x) ∈ V(K)` have the same image in `Y`, so
   they come from a point `σ x ∈ P(K)` (`exists_app_of_isPullback`). Along `𝒰`, `σ x ≫ g`
   equals `e.symm (f x)`, which converges to `v`: `e.symm` is continuous at `y`, and the
   comparison with scheme points is a homeomorphism (`isHomeomorph_schemeRingPointsEquiv`).
5. By properness of `g` on points (`IsProperMap.ultrafilter_le_nhds_of_tendsto`), the image
   ultrafilter `σ(𝒰)` converges to some `w₀ ∈ P(K)`. The point map of `q` is continuous
   (`continuous_schemePointsMap`), and `q(σ x) = x` on `W`. So `𝒰` converges to `q(w₀)`.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Corollary 5.12 and its
  proof, printed p.20.
