import Langlands.Automorphic.CuspidalWhittaker.WhittakerCoefficient
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating Whittaker coefficients along right-translation curves

Let `e : ℝ → GL_{r+1}(𝔸_K)` be a continuous curve and let `F, G` be functions on
`GL_{r+1}(𝔸_K)` with `d/ds F(g · e(s)) = G(g · e(s))` for every `g`. If `F` and `G` satisfy
the level-`k` properties of the Whittaker iteration, then the same relation holds for the
column coefficients and for the iterated Whittaker coefficients `descend k F` and
`descend k G`. The column coefficients are integrals over the compact torus `(𝔸_K / K)^{r+1}`,
so this is differentiation under the integral sign with a uniform bound coming from
compactness.
-/

noncomputable section

universe u

open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]

/-! ### Differentiation of torus integrals -/

section Torus

variable {ι : Type*} [Fintype ι]

/-- Differentiation under the torus integral: if `Φ s` and `Ψ s` are continuous periodic
functions, `Ψ` is jointly continuous and `∂ₛ Φ s y = Ψ s y`, then the torus integral of `Φ s`
has derivative the torus integral of `Ψ t` at `t`. -/
theorem hasDerivAt_torusIntegral {Φ Ψ : ℝ → (ι → Adeles K) → ℂ}
    (hΦ : ∀ s, IsPeriodic (Φ s)) (hΦc : ∀ s, Continuous (Φ s))
    (hΨ : ∀ s, IsPeriodic (Ψ s)) (hΨc : Continuous (Function.uncurry Ψ))
    (hd : ∀ y t, HasDerivAt (fun s => Φ s y) (Ψ t y) t) (t : ℝ) :
    HasDerivAt (fun s => torusIntegral ι (Φ s)) (torusIntegral ι (Ψ t)) t := by
  unfold torusIntegral
  have hq : IsOpenQuotientMap (Prod.map (id : ℝ → ℝ) (torusMk (K := K) (ι := ι))) :=
    IsOpenQuotientMap.id.prodMap isOpenQuotientMap_torusMk
  have hcont : Continuous fun p : ℝ × (ι → AdeleQuotient K) => Ψ p.1 (torusLift p.2) := by
    rw [hq.isQuotientMap.continuous_iff]
    convert hΨc using 1
    funext p
    exact (hΨ p.1).lift_mk p.2
  obtain ⟨C, hC⟩ := (isCompact_closedBall t 1 |>.prod
    (isCompact_univ : IsCompact (Set.univ : Set (ι → AdeleQuotient K)))).exists_bound_of_continuousOn
      hcont.continuousOn
  have hcΨ : ∀ s, Continuous fun p : ι → AdeleQuotient K => Ψ s (torusLift p) := fun s =>
    (hΨ s).continuous_lift (hΨc.comp (Continuous.prodMk_right s))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (E := ℂ)
    (μ := torusHaar K ι) (F := fun s p => Φ s (torusLift p))
    (F' := fun s p => Ψ s (torusLift p)) (x₀ := t) (bound := fun _ => C)
    (closedBall_mem_nhds t one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s =>
      ((hΦ s).continuous_lift (hΦc s)).aestronglyMeasurable
  · exact integrable_of_continuous ((hΦ t).continuous_lift (hΦc t))
  · exact (hcΨ t).aestronglyMeasurable
  · exact ae_of_all _ fun p s hs => hC (s, p) ⟨hs, Set.mem_univ _⟩
  · exact integrable_const C
  · exact ae_of_all _ fun p s _ => hd (torusLift p) s

end Torus

/-! ### Curves of right translations -/

variable {r : ℕ}

/-- `G` is the derivative of `F` along right translation by the curve `e`:
`d/ds F(g · e(s)) = G(g · e(s))` for all `g` and `s`. -/
def HasCurveDeriv (e : ℝ → AdelicGL K (r + 1)) (F G : AdelicGL K (r + 1) → ℂ) : Prop :=
  ∀ (g : AdelicGL K (r + 1)) (t : ℝ), HasDerivAt (fun s => F (g * e s)) (G (g * e t)) t

/-- The column coefficient preserves the derivative relation. -/
theorem HasCurveDeriv.colCoeff {e : ℝ → AdelicGL K (r + 1)} (he : Continuous e) {c : ℕ}
    {F G : AdelicGL K (r + 1) → ℂ} (hF : LevelProps (c + 1) F) (hG : LevelProps (c + 1) G)
    (hd : HasCurveDeriv e F G) :
    HasCurveDeriv e (CuspidalWhittaker.colCoeff c F) (CuspidalWhittaker.colCoeff c G) := by
  intro g t
  by_cases h : c < r
  · simp only [colCoeff_eq h, fourierCoeff]
    refine hasDerivAt_torusIntegral
      (Φ := fun s y => F (colUnit (colIdx c h) y * (g * e s)) *
        conj (pairingCharacter (Pi.single (charIdx c h) 1) y))
      (Ψ := fun s y => G (colUnit (colIdx c h) y * (g * e s)) *
        conj (pairingCharacter (Pi.single (charIdx c h) 1) y)) ?_ ?_ ?_ ?_ ?_ t
    · exact fun s => (isPeriodic_col h hF.invariant _).mul (isPeriodic_conj_pairingCharacter _)
    · exact fun s => (continuous_col_apply h hF.continuous _).mul
        (continuous_conj_pairingCharacter _)
    · exact fun s => (isPeriodic_col h hG.invariant _).mul (isPeriodic_conj_pairingCharacter _)
    · refine Continuous.mul ?_ ((continuous_conj_pairingCharacter _).comp continuous_snd)
      exact hG.continuous.comp (((continuous_colUnit (colIdx c h)).comp continuous_snd).mul
        (continuous_const.mul (he.comp continuous_fst)))
    · intro y t'
      have h1 := (hd (colUnit (colIdx c h) y * g) t').mul_const
        (conj (pairingCharacter (Pi.single (charIdx c h) (1 : K)) y))
      simp only [mul_assoc] at h1 ⊢
      exact h1
  · simp only [CuspidalWhittaker.colCoeff, dite_eq_right h]
    exact hd g t

/-- The iterated Whittaker coefficient preserves the derivative relation. -/
theorem HasCurveDeriv.descend {e : ℝ → AdelicGL K (r + 1)} (he : Continuous e) :
    ∀ k, k ≤ r → ∀ F G : AdelicGL K (r + 1) → ℂ, LevelProps k F → LevelProps k G →
      HasCurveDeriv e F G →
        HasCurveDeriv e (CuspidalWhittaker.descend k F) (CuspidalWhittaker.descend k G)
  | 0, _, _, _, _, _, hd => hd
  | k + 1, hk, F, G, hF, hG, hd =>
      HasCurveDeriv.descend he k (by omega) _ _ (hF.colCoeff (by omega))
        (hG.colCoeff (by omega)) (hd.colCoeff he hF hG)

end Langlands.Automorphic.CuspidalWhittaker
