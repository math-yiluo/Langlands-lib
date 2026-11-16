# The closed-fibre charts `Spec B_y`

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteChart`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. This module supports the proof of
Step 2a of Murre's induction (`MurreCompleteLocalStepStatement`; Bourbaki exp. 294, Case I,
Step 2a). Murre sets `B_i = lim_n B_{n,i}` and uses (F3) to get an element `ξ_i ∈ F(Spec B_i)`.
Here `B_y` is the inverse limit of the stalk tower `Bk e y n` from `MurreCompleteFibre`, one ring
for each point `y` of the representing scheme `Y 0` over `Spec (R/m)`. The module also proves the
properties of `ξ_y` at the closed point that Murre's Lemma 3 needs.

## (F3) for `ovR` (section `Adic`)

`ovR R A` is the Library's `Spec A` over `Spec R`, and `homR` is the morphism associated with an
`R`-algebra map. (F3) itself, `AdicLimits`, is stated with `algebraOver`; the Library's
`towerIso` converts between the two.

* `algebraOverBase_eq`: the structure morphism of `Spec (A/I)` over `Spec A`, written as
  `towerIso ≫ homR (mkₐ I)`.
* `algHomOver_towerIso`: the same for a quotient map `A/I → A/J`.
* `map_towerIso_injective`: restriction along `towerIso` is injective.
* `exists_homR`: every morphism `ovR R T' ⟶ ovR R T` is `homR` of an `R`-algebra map.
* `adic_unique` and `adic_exists`: the uniqueness and existence halves of (F3) over a complete
  local noetherian `R`-algebra, stated with `ovR`/`homR`.

## The chart ring (section `Limit`)

Let `R` be complete local noetherian. Let `Y k` represent `F` over `Spec (R/m^(k+1))` through a
formally unramified morphism `q k`, locally of finite type.

* `ChartRing e y` is `limitAlg (Bk e y) (transition e y)`, and `chartProj e y n` is the
  projection `B_y → Bk e y n`. The hypotheses of `MurreCompleteLimit` hold by
  `transition_surjective`, `transition_ker_linear`, `B0_finite` and `B0_isField`. So `B_y` is a
  finite `R`-module (`chart_spec`), local, noetherian, formally unramified over `R`, and complete
  for its maximal ideal. Its maximal ideal is `m B_y` (`chart_maximalIdeal`), and the kernel of
  `chartProj n` is `m_{B_y}^(n+1)` (`chartProj_ker`).
* `qIso`: the isomorphism `Bk e y n ≅ B_y / m_{B_y}^(n+1)`.
* `sAux`, `sFam`, `sFam_compat`: transport the `ξk e y n` along `qIso` to get a compatible family
  over the quotients `B_y / m_{B_y}^n`.
* `chartElem e hF3 y`: the element `ξ_y ∈ F(Spec B_y)` that `adic_exists` gives for this family.
  It restricts to the family (`map_mk_chartElem`), and its restriction along `chartProj n` is
  `ξk e y n` (`map_chartProj_chartElem`).

## Properties at the closed point

* `quotLift`, `quotLift_fac`: an `R`-algebra `A` killing `m^(k+1)` lies over
  `Spec (R/m^(k+1))`.
* `exists_factor_chartProj_zero`, `exists_factor_chartProj`: an `R`-algebra map from `B_y`
  killing `m^(k+1)` factors through `chartProj k` (via `qIso`).
* `cls_closedPoint_of_residue`: take a local `R`-algebra `A` killing `m^(k+1)` and an element
  `η ∈ F(Spec A)` whose restriction to the residue field comes from `ξ_y`. Then the classifying
  morphism of `η` at level `k` sends the closed point to `pt e y k`. The proof factors the
  residue-field map through the field `Bk e y 0`. It then compares classifying morphisms at
  levels `0` and `k` with `cls_towerMap` and `cls_map`, and uses `towerMap_pt`.
* `chart_lift` (pro-representability at the closed point): such an `η` is a restriction of
  `ξ_y`. Apply `exists_levelElem` at level `k`, then compose with `chartProj k`.
* `chart_inj_level`: two `R`-algebra maps from `B_y` to an `R`-algebra killing `m^(k+1)` that
  restrict `ξ_y` to the same element are equal (`exists_factor_chartProj`,
  `levelElem_injective`).
* `chart_cover`: every element of `F` over a field killing `m` is a restriction of some `ξ_y`.
  Take `y` to be the image of the closed point under the classifying morphism at level `0`.
* `chart_infinitesimallyEtaleAt_closedPoint`: `ξ_y` is infinitesimally étale at the closed point
  of `Spec B_y`. Take a local artinian `A`, a nilpotent ideal `J`, a point
  `u₀ : Spec (A/J) ⟶ Spec B_y` at the closed point, and `v ∈ F(Spec A)` with `ξ_y ∘ u₀` equal to
  `v` restricted to `Spec (A/J)`. Since `u₀` lands at the closed point, `A` is local over `R`, so
  `A` kills some `m^(N+1)`. Now `u₀` is `homR ψ₀` up to `towerIso`. The residue-field restriction
  of `v` comes from `ξ_y`, so `chart_lift` gives `ψ : B_y → A` with `ξ_y ∘ ψ = v`. Then
  `chart_inj_level` shows that `ψ` extends `ψ₀` and is unique.
