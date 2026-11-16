# The closed-fibre charts are infinitesimally étale

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteEtale`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. It supports the proof of Step 2a
of Murre's induction (`MurreCompleteLocalStepStatement`, Bourbaki exp. 294, Case I, Step 2a).
The module proves hypothesis `het` of `unramifiedRepresentable_of_chartEtale`
(`MurreCompleteAssembly`): `ξ_y` is infinitesimally étale at every non-closed point of
`Spec B_y`.

## `infinitesimallyEtaleAt_chart`

Hypotheses:

* `R` is complete local noetherian.
* `L` is local noetherian, and finite and étale over `R`.
* `B` is local, and `π : L → B` is a surjective `R`-algebra map.
* `ξB ∈ F(Spec B)` is a monomorphism and pro-representable (`ProRep`).
* `F` satisfies (F5) and (F7), and is representable over the punctured spectrum of `R`.

Conclusion: `ξB` is infinitesimally étale at every point `z ≠ closedPoint B` of `Spec B`.

Proof.

* Let `w0 = chartInv(z)` be the corresponding point of `Spec (L/I)`. Its prime in `L` is
  `π⁻¹(z)`, which is not `m_L` because `z` is not the closed point.
* Since `L` is noetherian, choose a prime `Q₀ ⊇ P_{w0}` maximal among the primes `≠ m_L`
  (`set_has_maximal_iff_noetherian`). Let `w` be its image in `Spec (L/I)`. Then
  `dim L/P_w = 1` and `w0 ≤ w`.
* Level at `w`. The primes of `O_w` contract into `Q₀`. Since `L` is integral over `R` and `Q₀`
  is not maximal, `Q₀ ∩ R ≠ m_R` (`Ideal.isMaximal_of_isIntegral_of_isMaximal_under`). So
  `Spec O_w → Spec R` lands in the punctured spectrum, and `nonempty_level_of_range` gives a
  level.
* `infinitesimallyEtaleAt_of_killAt_surjective` and `killAt_chart` (`MurreCompleteHet`) show that
  `ξB ∘ chartHom` is infinitesimally étale at `w`.
* Generization (`infinitesimallyEtaleAt_of_le_of_level`) gives the same at `w0`.
* Restrict along the open immersion `chartInv` (`Charts.infinitesimallyEtaleAt_restrict`) and use
  `chartInv ≫ chartHom = 𝟙`.

## `chartElem_infinitesimallyEtaleAt`

Let `F` satisfy `MurreConditions` and be representable over the punctured spectrum. Then for
every `y : Y 0`, `chartElem e hF3 y` is infinitesimally étale at every non-closed point of
`Spec B_y`.

Proof.

* `B_y` is local, finite and formally unramified over `R`, and henselian, being complete
  (Mathlib's `IsAdicComplete` henselian instance). Its structure map is local
  (`isLocalHom_of_finite`).
* `exists_etaleCover` gives `L` and `π`. `L` is noetherian, being finite over `R`.
* Apply `infinitesimallyEtaleAt_chart`. Monomorphism: `chartElem_isMonoElement` (from (F1b) and
  (F6)). Pro-representability: `chart_lift_complete`.
