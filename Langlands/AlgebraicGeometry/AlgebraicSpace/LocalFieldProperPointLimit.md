# Corollary 5.6 for algebraic spaces from the valuative criterion

Author: Worker 78.

This module proves `LocalFieldProperPointLimit.localFieldProperPointMap_of_valuative`:

```
SpaceValuativeExistenceStatement.{u} → LocalFieldProperPointMapStatement.{u}
```

that is, the valuative existence criterion for quasi-compact, separated, universally closed
morphisms of algebraic spaces (Stacks Project, *Morphisms of Algebraic Spaces*,
Lemma 67.42.3, (1) ⇒ (3)) implies Conrad's Corollary 5.6 for algebraic spaces (*Weil and
Grothendieck approaches to adelic points*, printed p.16). This proves
`LocalFieldProperPointValuativeReductionStatement`.

## Route

Conrad proves Corollary 5.6 with Chow's lemma for algebraic spaces. The implemented proof
instead applies the valuative criterion over the ring `O` of convergent germs in an
ultrapower `L = K^I/𝒰` of the local field `K`, as in the Library's scheme case
`PointTopology.exists_limit_of_valuationSubring`. Archimedean fields are covered: only local
compactness, completeness and non-discreteness of `K` are used.

## Auxiliary lemmas

- `tendsto_affine_iff`, `affineSchemePointEquiv_pi`: on an affine scheme, convergence of
  rational points is convergence of coordinates (`schemePointTopology_eq_affine`), and the
  coordinates of a point with values in `K^I` are the families of coordinates of its
  components.
- `exists_convergentGerm_point`: if the components of `P ∈ V(K^I)`, `V` affine, converge to
  `v₀` along `𝒰`, the germs of its coordinates lie in `O`, giving `v_O ∈ V(O)` whose image in
  `V(L)` is that of `P` and whose reduction by `standardPart` is `v₀`.
- `pointMap_eq_of_comp`, `comp_eq_pointMap`: translation between chart points and the Yoneda
  form of morphisms.
- `tendsto_of_chart_lift` (convergence through a chart): let `P ∈ X'(K^I)` have components
  `p i`, let `c : W → X'` be an affine étale chart, and let `z ∈ W(O)` have image in `X'(L)`
  equal to that of `P`. Form the represented pullback `E = W ×_{X'} Spec K^I`, an étale, hence
  locally finitely presented, scheme over `Spec K^I`. The pair `(z_L, Spec L → Spec K^I)` is an
  `L`-point of `E`; by `exists_stage_ringPoint` it comes from a point over
  `K^I ⧸ vanishing K A` for some `A ∈ 𝒰`. Its image `w'` in `W` has components `w'_i ∈ W(K)`,
  `i ∈ A`, with `c(w'_i) = p i`, and coordinates whose germs are those of `z`; hence the
  `w'_i` converge to the reduction `z₀` of `z`, and by continuity of the chart map `p`
  converges to `c(z₀)`.
- `spec_algebraMap_tower`, `towerTest`, `towerHom`, `towerInv`, `homMk_eq_towerHom_comp`:
  identification of the test object `Spec L → Spec O → Spec K` of the valuative statement
  with `Spec L` over `Spec K`.
- `locallyOfFiniteTypeOverBase_of_finiteType`: finite type implies locally of finite type.

## The core lemma `exists_limit_fibre`

Let `f : X ⟶ Y` be quasi-compact, separated and universally closed, `X` locally of finite
type, `g : h_V ⟶ Y` étale with `V` affine, and `X' = X ×_Y h_V` (`ChartFibre.space`, a
separated algebraic space of finite type over `K`). Let `p : I → X'(K)` be a family whose
`V`-coordinates converge to `v₀` along `𝒰`. Then:

1. `SpaceProductPoints.separatedProductPoints_surjective` gives `P ∈ X'(K^I)` with components
   `p i`; let `ξ ∈ X'(L)` be its image.
2. `exists_convergentGerm_point` gives `v_O ∈ V(O)` lifting the `V`-component of `ξ` and
   reducing to `v₀`.
3. The valuative criterion applied to `f`, the valuation ring `O` with fraction field `L`, the
   point `ξ_X ∈ X(L)` and `g(v_O) ∈ Y(O)` (the square commutes because `f(ξ_X) = g(ξ_V)`)
   gives `a ∈ X(O)` lifting `ξ_X` with `f(a) = g(v_O)`. So `a' = (a, v_O) ∈ X'(O)` lifts `ξ`.
4. Let `x'` be the reduction of `a'`; its `V`-component is `v₀`. Choose an affine étale chart
   `c : W → X'` with a rational point over `x'` (`exists_affine_chart_pointMap_eq`). Since
   `O` is henselian (`convergentGerms_henselian`) with residue map onto `K`,
   `ProductPointsLocalLift.exists_point_of_field_point` lifts `a'` to `z ∈ W(O)`.
5. `tendsto_of_chart_lift` shows that `p` converges to `c(z₀) = x'`.

## The main theorem

By `isProperMap_iff_ultrafilter` it suffices, besides continuity
(`continuous_ringPointsMap`), to show: if an ultrafilter `𝒰` on `X(K)` has image converging to
`y ∈ Y(K)`, then `𝒰` converges to some `x` with `f(x) = y`. Choose an affine étale chart
`V → Y` with `v₀ ↦ y`. Its point map is open (`isOpenMap_schemePointsMap`), so
`exists_ultrafilter_lift` lifts `𝒰` to an ultrafilter `𝒲` on `X'(K)` whose `V`-component
converges to `v₀`. By `RingPointsSmall.small_ringPoints` the type `X'(K)` is `u`-small, so
`𝒲` is transported to an ultrafilter on `Shrink X'(K)`, a type in the universe `u`. The core
lemma gives a limit `x'` of `𝒲` over `v₀`; its first component `x` satisfies `f(x) = y`, and
`𝒰` converges to `x` by continuity of the projection `X'(K) → X(K)`.

The local field `K` is complete (proper, by `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`),
henselian as a valued field (`completeHenselianValuedField`) and non-discrete.
