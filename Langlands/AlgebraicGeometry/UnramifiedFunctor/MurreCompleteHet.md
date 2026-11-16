# The lifting condition at the one-dimensional points of a chart

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteHet`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. This module supports the proof of
Step 2a of Murre's induction (`MurreCompleteLocalStepStatement`, Bourbaki exp. 294, Case I,
Step 2a). It connects the lifting argument of `MurreCompleteStar` to the Library's lifting
condition `EtaleLocus.KillAt` on the chart `Spec (L/I)`.

## Section `ChartIso`

Let `π : L → B` be a surjective `R`-algebra map with kernel `I`.

* `chartHom π hπ : EtaleLocus.chart R L I ⟶ ovR R B`: the isomorphism `Spec (L/I) ≅ Spec B`
  over `Spec R`. It is the Library's `towerIso`, followed by `homR` of the inverse of
  `Ideal.quotientKerAlgEquivOfSurjective`. `chartInv` is its inverse (`chartInv_chartHom`,
  `chartHom_chartInv`, using `homR_comp` and `homR_id`). Hence `chartInv` is an isomorphism, and
  its underlying morphism is an open immersion.

## Section `Kill`: `killAt_chart`

Let `R` be complete local noetherian and `L` local noetherian, finite and formally unramified over
`R`. Let `ξB ∈ F(Spec B)` be a monomorphism and pro-representable (`ProRep`), and assume (F5)
and (F7). Let `w` be a point of `Spec (L/I)` whose prime `P_w` of `L` satisfies
`dim L/P_w = 1`: `P_w ≠ m_L`, and every prime above `P_w` is `m_L`. Then for every surjection
`δ'` from `O_w = L_{P_w}` onto a local artinian ring `A`, the lifting condition
`KillAt (ξB ∘ chartHom) w A (δ' ∘ (L → O_w))` holds.

Proof. Take the data of `KillAt`: a nilpotent ideal `J`, a point `u₀ : Spec (A/J) ⟶ Spec (L/I)`
at `w` compatible with `β = δ' ∘ (L → O_w)`, and `v ∈ F(Spec A)` with
`(ξB ∘ chartHom) ∘ u₀ = v|_{A/J}`. Make `A` an `R`-algebra through `β`. Then:

* `β⁻¹(m_A) = P_w`, since `δ'` is local and `Localization.AtPrime.under_maximalIdeal`.
* Every `a ∈ A` is `δ'(r/s)`, so `a β(s) = β(r)` (`IsLocalization.mk'_surjective`).
* `I ⊆ P_w` (`le_primeOf`).
* `u₀` is `Spec γ₀` for a ring map `γ₀ : L/I → A/J` with `γ₀ ∘ mk = mk ∘ β`
  (`exists_specMap_ofHom`, `specMap_ofHom_inj`). In particular `β(I) ⊆ J`.
* `βb : B → A/β(I)A` is induced by `mk ∘ β` (`AlgHom.liftOfSurjective`).
* Writing `u₀ ≫ chartHom` as `towerIso ≫ homR (γ₀ ∘ q⁻¹)` gives `ξB ∘ (γ₀ ∘ q⁻¹) = v|_{A/J}`
  (`map_towerIso_injective`, `algebraOverBase_eq`).
* Condition (F5) (`NilpotentInjective`) on the local artinian ring `A/β(I)A` with the nilpotent
  ideal `J (A/β(I)A)` upgrades this to `v|_{A/β(I)A} = ξB ∘ βb`. Both sides restrict to the same
  element of `F` over `(A/β(I)A)/J ≅ A/J` (through the map `κ`).

Now `star` (`MurreCompleteStar`) gives `β(I) = 0`, which is the conclusion of `KillAt`.
