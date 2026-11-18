import Langlands.Representation.Archimedean.RealLeviLimit

/-!
# The limit along a standard parabolic subgroup: value form

Let `Q` be the standard parabolic subgroup of `GL_N(ℝ)` with diagonal blocks of sizes
`sz_0, …, sz_{c-1}`, `d_s = diag(s^{cls p})` its central scaling, and `ds` a list of real blocks
of rank `N` as in `RealLeviLimitStatement`. For `u` in the dual principal series and `h` in the
standard module of `ds`, both `O(N)`-finite, let

`Θ(u, h) = ∫_{K_M} ∫_{N̄_Q} c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) dX dκ`

be the torus-averaged limit pairing of module `RealLeviLimit`. The module `RealLeviLimit`
proves `Θ(u, h) = 0` when all matrix coefficients `∫_{O(N)} u(κ g) h(κ) dκ` vanish. Here:

* `exists_integral_torus_scale_eq`: at each scale `s > 0` the approximating integral of `Θ` is
  a fixed multiple, depending only on `χ`, the torus slots and `s`, of the single matrix
  coefficient `∫_{O(N)} u(κ d_s) h(κ) dκ`;
* `tendsto_integral_scale`: the approximating integrals converge to `Θ(u, h)` as `s → ∞`;
* `integral_coeffs_eq_of_eq` (**value form**): if two pairs `(u, h)` and `(u', h')` have the
  same matrix coefficients at every `d_s`, then `Θ(u, h) = Θ(u', h')`.

The proofs follow those of `RealLeviLimit.integral_torus_scale_eq_zero` and
`RealLeviLimit.integral_coeffs_eq_zero`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealParabolicLimitValue

open RealInducedBlockBound RealInducedTorusCore RealLeviChart GramFormula RealLeviTorus
  RealLeviLimit
open RealPrincipalSeriesDuality MaximalParabolicIntegration PartialJacquet JacquetLimit

attribute [local instance] measurableSpaceK

local instance borelSpaceK_lv (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

attribute [local instance] RealBlockLimit.secondCountableTopology_unitaryCompact

variable {c : ℕ} {sz : Fin c → ℕ}

/-! ## A fixed scale -/

section FixedScale

/-- The `K_M × N̄_Q × torus` integral of a smooth modulus covariant function `G` is a fixed
multiple of its `O(N)`-integral, given the integration formula with constant `C`. -/
theorem integral_torus_eq (hT1 : RealLeviChartIntegrableStatement) {C : ℝ} (hC : 0 < C)
    (hT3 : ∀ F : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ,
      ContMDiff (matrixModel ℝ (∑ i, sz i)) 𝓘(ℝ, ℂ) ∞ F → IsModulusCovariant F →
      (∀ κ : ∀ i, unitaryCompact ℝ (sz i),
        Integrable fun X : Coord sz → ℝ =>
          F (lowerGL sz X * blockDiagGL sz fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))) ∧
      ∫ κ, F (κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) ∂haarK (∑ i, sz i) =
        (C : ℂ) * ∫ κ : (∀ i, unitaryCompact ℝ (sz i)),
          (∫ X : Coord sz → ℝ,
            F (lowerGL sz X * blockDiagGL sz fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)))
          ∂Measure.pi fun i => haarK (sz i))
    {G : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hGs : ContMDiff (matrixModel ℝ (∑ i, sz i)) 𝓘(ℝ, ℂ) ∞ G) (hG : IsModulusCovariant G)
    (L : List (Slot (∑ i, sz i)))
    (hL : ∀ s ∈ L, cls sz ⟨s.p, by have := s.hp; omega⟩ = cls sz ⟨s.p + 1, s.hp⟩) :
    ∫ κ, (∫ X : Coord sz → ℝ, (∫ θ, G (torusElem L θ * (lowerGL sz X * bdK sz κ))
        ∂torusMeasure L.length)) ∂Measure.pi (fun i => haarK (sz i)) =
      (torusMeasure L.length).real Set.univ •
        ((C : ℂ)⁻¹ * ∫ κ, G (κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) ∂haarK (∑ i, sz i)) := by
  have hτ : ∀ θ, torusElem L θ ∈ blockOrth sz := torusElem_mem_blockOrth L hL
  have hGc : Continuous G := hGs.continuous
  -- the integral formula
  have hJ : ∫ κ, (∫ X : Coord sz → ℝ, G (lowerGL sz X * bdK sz κ))
      ∂Measure.pi (fun i => haarK (sz i)) =
        (C : ℂ)⁻¹ * ∫ κ, G (κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) ∂haarK (∑ i, sz i) := by
    have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
    rw [(hT3 G hGs hG).2]
    exact (inv_mul_cancel_left₀ hC0 _).symm
  -- invariance under the torus element
  have hθ : ∀ θ, ∫ κ, (∫ X : Coord sz → ℝ, G (torusElem L θ * (lowerGL sz X * bdK sz κ)))
      ∂Measure.pi (fun i => haarK (sz i)) =
        (C : ℂ)⁻¹ * ∫ κ, G (κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) ∂haarK (∑ i, sz i) := by
    intro θ
    have e1 : ∀ κ : ∀ i, unitaryCompact ℝ (sz i),
        (∫ X : Coord sz → ℝ, G (torusElem L θ * (lowerGL sz X * bdK sz κ))) =
          ∫ X : Coord sz → ℝ, G (lowerGL sz X * (torusElem L θ * bdK sz κ)) := by
      intro κ
      have : ∀ X, G (torusElem L θ * (lowerGL sz X * bdK sz κ)) =
          G (lowerGL sz (adCoord (torusElem L θ : Matrix _ _ ℝ) X) *
            (torusElem L θ * bdK sz κ)) := by
        intro X
        rw [← mul_assoc, mul_lowerGL (hτ θ), mul_assoc]
      simp_rw [this]
      exact integral_adCoord (hτ θ)
        (fun Y => G (lowerGL sz Y * (torusElem L θ * bdK sz κ)))
    simp_rw [e1]
    have h2 := integral_blockOrth_mul
      (fun g => ∫ X : Coord sz → ℝ, G (lowerGL sz X * g)) (hτ θ)
    exact h2.trans hJ
  -- exchange the torus integral with the others
  obtain ⟨CG, hCG⟩ := exists_bound_unitaryCompact hGc
  have hT1' := hT1 c sz (fun _ => -1) (fun _ _ => by norm_num) (fun _ _ _ _ => by norm_num)
  have hB : Integrable fun X : Coord sz → ℝ => CG * gramBound (fun _ => -1) X :=
    hT1'.const_mul CG
  have hBc : Continuous fun X : Coord sz → ℝ => CG * gramBound (fun _ => -1) X :=
    continuous_const.mul (continuous_gramBound _)
  rw [integral_swap_torus (μ := torusMeasure L.length)
    (b := fun X θ => CG * gramBound (fun _ => -1)
      (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X))
    (continuous_integrand hGc ((continuous_torusElem L).comp continuous_snd)
      (continuous_snd.comp continuous_fst) (continuous_fst.comp continuous_fst))
    (integrable_comp_adCoord hBc hB (continuous_torusElem L) hτ)
    (fun θ => (measurePreserving_adCoord (hτ θ)).integrable_comp_of_integrable hB)
    (fun κ X θ => ?_)]
  · simp_rw [hθ]
    exact integral_const _
  · rw [← mul_assoc, mul_lowerGL (hτ θ), mul_assoc]
    exact norm_modulusCovariant_le hG hCG _
      (mem_unitaryCompact_of_mem_blockOrth (mul_mem (hτ θ) (bdK_mem_blockOrth κ)))

/-- **The approximating integral at the scale `s`.** There is a constant `C > 0`, depending
only on the block sizes, such that for every `s > 0`
`∫_{K_M} ∫_X ∫_θ u(τ_θ n̄(X_s) diag(κ)) h(τ_θ n̄(X) diag(κ)) dθ dX dκ` equals
`c(s)⁻¹ · |torus| · C⁻¹ · ∫_{O(N)} u(κ d_s) h(κ) dκ`, where `c(s)` is the value at `d_s` of the
character of the dual principal series. -/
theorem exists_integral_torus_scale_eq (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement) (c : ℕ) (sz : Fin c → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}, IsSignedPower χ e →
      ∀ {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ},
      u ∈ principalSeries ℝ (∑ i, sz i) (dualChar χ) →
      h ∈ principalSeries ℝ (∑ i, sz i) χ →
      ∀ (L : List (Slot (∑ i, sz i))),
      (∀ s ∈ L, cls sz ⟨s.p, by have := s.hp; omega⟩ = cls sz ⟨s.p + 1, s.hp⟩) →
      ∀ {s : ℝ} (hs : 0 < s),
      ∫ κ, (∫ X : Coord sz → ℝ, (∫ θ,
          u (torusElem L θ * (lowerGL sz (scaleCoord sz s X) * bdK sz κ)) *
            h (torusElem L θ * (lowerGL sz X * bdK sz κ)) ∂torusMeasure L.length))
        ∂Measure.pi (fun i => haarK (sz i)) =
        (principalSeriesCharacter ℝ (∑ i, sz i) (dualChar χ)
          (fun p => Units.mk0 (scaleVec sz s p) (scaleVec_pos sz hs p).ne'))⁻¹ *
        ((torusMeasure L.length).real Set.univ •
          ((C : ℂ)⁻¹ * ∫ κ, u ((κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) * scaleGL sz hs) *
            h κ ∂haarK (∑ i, sz i))) := by
  obtain ⟨C, hC, hT3'⟩ := hT3 c sz
  refine ⟨C, hC, fun {χ e} hχ {u h} hu hh L hL {s} hs => ?_⟩
  have hτ : ∀ θ, torusElem L θ ∈ blockOrth sz := torusElem_mem_blockOrth L hL
  set d : Langlands.GeneralLinear (∑ i, sz i) ℝ := scaleGL sz hs with hd
  have hud := rightTranslation_mem_principalSeries (χ := dualChar χ) hu d
  set G : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ := fun y => u (y * d) * h y with hGdef
  have hGs : ContMDiff (matrixModel ℝ (∑ i, sz i)) 𝓘(ℝ, ℂ) ∞ G := contMDiff_mul_fun hud.1 hh.1
  have hG : IsModulusCovariant G := by
    intro z v y
    simp only [hGdef]
    rw [mul_assoc _ y, hu.2 z v, hh.2 z v y, ← principalSeriesCharacter_dual_mul hχ]
    ring
  -- the scaling identity
  set c' := principalSeriesCharacter ℝ (∑ i, sz i) (dualChar χ)
    (fun p => Units.mk0 (scaleVec sz s p) (scaleVec_pos sz hs p).ne') with hc'def
  have hdu : ∀ y, u (d * y) = c' * u y := fun y => by
    have := hu.2 (fun p => Units.mk0 (scaleVec sz s p) (scaleVec_pos sz hs p).ne') 1 y
    simpa [hd, scaleGL] using this
  have hc'0 : c' ≠ 0 := by
    rw [← norm_ne_zero_iff, hc'def, norm_principalSeriesCharacter hχ.dual]
    exact (Finset.prod_pos fun l _ =>
      Real.rpow_pos_of_pos (abs_pos.mpr (Units.ne_zero _)) _).ne'
  have hpt : ∀ (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ) (θ : Fin L.length → ℝ),
      u (torusElem L θ * (lowerGL sz (scaleCoord sz s X) * bdK sz κ)) *
        h (torusElem L θ * (lowerGL sz X * bdK sz κ)) =
      c'⁻¹ * G (torusElem L θ * (lowerGL sz X * bdK sz κ)) := by
    intro κ X θ
    have hk := bdK_mem_blockOrth (sz := sz) κ
    have e2 : torusElem L θ * (lowerGL sz X * bdK sz κ) * d =
        d * (torusElem L θ * (lowerGL sz (scaleCoord sz s X) * bdK sz κ)) := by
      rw [mul_assoc, mul_assoc, mul_scaleGL hk hs, ← mul_assoc (lowerGL sz X),
        lowerGL_mul_scaleGL sz hs, mul_assoc, ← mul_assoc (torusElem L θ),
        mul_scaleGL (hτ θ) hs, mul_assoc]
    simp only [hGdef]
    rw [e2, hdu, mul_assoc c', inv_mul_cancel_left₀ hc'0]
  simp_rw [hpt, integral_const_mul]
  rw [integral_torus_eq hT1 hC hT3' hGs hG L hL]

end FixedScale

/-! ## The limit -/

section Limit

open RealInducedStandardBound RealStrictCharacterLanglandsQuotient

/-- **Convergence of the approximating integrals.** Under the hypotheses of
`RealLeviLimitStatement` on `ds`, the integrals
`∫_{K_M} ∫_X ∫_θ u(τ_θ n̄(X_{n+1}) diag(κ)) h(τ_θ n̄(X) diag(κ)) dθ dX dκ` converge to
`∫_{K_M} ∫_X c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) dX dκ` as `n → ∞`. -/
theorem tendsto_integral_scale (hT1 : RealLeviChartIntegrableStatement) {ds : List RealBlock}
    (hN : realRank ds = ∑ i, sz i)
    (hanti : ∀ p q : Fin (∑ i, sz i), p ≤ q →
      realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p)
    (hstrict : ∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p)
    {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hh : h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
      (unitaryCompact ℝ (∑ i, sz i))) :
    Tendsto (fun n : ℕ => ∫ κ, (∫ X : Coord sz → ℝ, (∫ θ,
        u (torusElem (slots ds (∑ i, sz i)) θ *
          (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) X) * bdK sz κ)) *
        h (torusElem (slots ds (∑ i, sz i)) θ * (lowerGL sz X * bdK sz κ))
          ∂torusMeasure (slots ds (∑ i, sz i)).length))
        ∂Measure.pi (fun i => haarK (sz i))) atTop
      (𝓝 (∫ κ, (∫ X : Coord sz → ℝ, coeffs (zeroModes (slots ds (∑ i, sz i)))
        (fun x => u (x * bdK sz κ) * h (x * (lowerGL sz X * bdK sz κ))) 1)
        ∂Measure.pi (fun i => haarK (sz i)))) := by
  set L := slots ds (∑ i, sz i) with hLdef
  set t := realPositionBlockExponent ds with htdef
  have hpsu : u ∈ principalSeries ℝ (∑ i, sz i) (dualChar (realPositionCharacter ds)) := hu.1
  have hps : h ∈ principalSeries ℝ (∑ i, sz i) (realPositionCharacter ds) := hh.1.1
  have huc : Continuous u := hpsu.1.continuous
  have hhc : Continuous h := hps.1.continuous
  have hL := slots_cls_eq (sz := sz) hstrict
  have hτ : ∀ θ, torusElem L θ ∈ blockOrth sz := torusElem_mem_blockOrth L hL
  have hT : Continuous (torusElem L) := continuous_torusElem L
  have hτK : ∀ θ, torusElem L θ ∈ unitaryCompact ℝ (∑ i, sz i) :=
    torusElem_mem_unitaryCompact L
  -- the torus-pairing bound
  obtain ⟨C0, hC0⟩ := exists_bound hN hu hh
  set C := max C0 0 with hCdef
  -- the exponents
  have hdrop : ∀ l : ℕ, 0 < l → l < ∑ i, sz i → t l ≤ t (l - 1) := fun l hl hlN =>
    hanti ⟨l - 1, by omega⟩ ⟨l, hlN⟩ (Fin.mk_le_mk.mpr (Nat.sub_le l 1))
  set γ : Fin (∑ i, sz i) → ℝ := fun l => gammaExp t l with hγ
  have hγ0 : ∀ l, γ l ≤ 0 := fun l => by
    rcases Nat.eq_zero_or_pos (l : ℕ) with h' | h'
    · simp only [hγ, gammaExp, h', ↓reduceIte]
      norm_num
    · linarith [gammaExp_le t h' (hdrop l h' l.2)]
  have hBi : Integrable (gramBound (sz := sz) γ) :=
    hT1 c sz γ (fun l hl => gammaExp_le t hl (hdrop l hl l.2)) fun k l hkl hcls => by
      have h1 := hstrict k l hcls
      have h2 : (k : ℕ) = (l : ℕ) - 1 := by omega
      refine gammaExp_lt t (by omega) ?_
      rw [← h2]
      exact h1
  have hBc : Continuous (gramBound (sz := sz) γ) := continuous_gramBound γ
  have hprod := integrable_comp_adCoord hBc hBi (μ := torusMeasure L.length) hT hτ
  set D : (Coord sz → ℝ) → ℝ := fun X => C * ∫ θ, gramBound γ
    (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X)
      ∂torusMeasure L.length with hDdef
  have hDi : Integrable D := hprod.integral_prod_left.const_mul C
  have hBθ : ∀ X : Coord sz → ℝ, Integrable (fun θ => gramBound γ
      (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X))
      (torusMeasure L.length) := fun X => by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun θ => ?_)
    · exact (hBc.comp (continuous_adCoord_prod.comp
        ((Units.continuous_val.comp hT).prodMk continuous_const))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (gramBound_nonneg _ _)]
      exact gramBound_le_one hγ0 _
  -- the integrands
  set Ψ : ℕ → (∀ i, unitaryCompact ℝ (sz i)) → (Coord sz → ℝ) → ℂ := fun n κ X =>
    ∫ θ, u (torusElem L θ * (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) X) * bdK sz κ)) *
      h (torusElem L θ * (lowerGL sz X * bdK sz κ)) ∂torusMeasure L.length with hΨ
  set Ψ' : (∀ i, unitaryCompact ℝ (sz i)) → (Coord sz → ℝ) → ℂ := fun κ X =>
    ∫ θ, u (torusElem L θ * bdK sz κ) * h (torusElem L θ * (lowerGL sz X * bdK sz κ))
      ∂torusMeasure L.length with hΨ'
  have hcont : ∀ n : ℕ, Continuous fun q : ((∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ)) ×
      (Fin L.length → ℝ) =>
      u (torusElem L q.2 * (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) q.1.2) * bdK sz q.1.1)) *
        h (torusElem L q.2 * (lowerGL sz q.1.2 * bdK sz q.1.1)) := fun n =>
    (continuous_integrand huc (hT.comp continuous_snd)
      ((continuous_scaleCoord _).comp (continuous_snd.comp continuous_fst))
      (continuous_fst.comp continuous_fst)).mul
    (continuous_integrand hhc (hT.comp continuous_snd) (continuous_snd.comp continuous_fst)
      (continuous_fst.comp continuous_fst))
  -- domination
  have hbound : ∀ (n : ℕ) (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ),
      ‖Ψ n κ X‖ ≤ D X := by
    intro n κ X
    have hs1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith
    have hs0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set y1 := lowerGL sz (scaleCoord sz ((n : ℝ) + 1) X) * bdK sz κ with hy1
    set y2 := lowerGL sz X * bdK sz κ with hy2
    have e1 : Ψ n κ X = coeffs (zeroModes L) (fun x => u (x * y1) * h (x * y2)) 1 := by
      rw [coeffs_eq_integral (F := fun x => u (x * y1) * h (x * y2))
        ((huc.comp (continuous_id.mul continuous_const)).mul
          (hhc.comp (continuous_id.mul continuous_const))) L 1]
      simp only [mul_one, hΨ]
      rfl
    have hE1 := (contMDiff_expFun (∑ i, sz i) fun l => -t l).continuous
    have hE2 := (contMDiff_expFun (∑ i, sz i) t).continuous
    have e2 : coeffs (zeroModes L) (fun x => expFun (∑ i, sz i) (fun l => -t l) (x * y1) *
        expFun (∑ i, sz i) t (x * y2)) 1 = ∫ θ, expFun (∑ i, sz i) (fun l => -t l)
          (torusElem L θ * y1) * expFun (∑ i, sz i) t (torusElem L θ * y2)
          ∂torusMeasure L.length := by
      rw [coeffs_eq_integral (F := fun x => expFun (∑ i, sz i) (fun l => -t l) (x * y1) *
        expFun (∑ i, sz i) t (x * y2)) ((hE1.comp (continuous_id.mul continuous_const)).mul
        (hE2.comp (continuous_id.mul continuous_const))) L 1]
      simp only [mul_one]
    have hpt : ∀ θ, ‖expFun (∑ i, sz i) (fun l => -t l) (torusElem L θ * y1) *
        expFun (∑ i, sz i) t (torusElem L θ * y2)‖ ≤ gramBound γ
          (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X) := by
      intro θ
      have hk : torusElem L θ * bdK sz κ ∈ unitaryCompact ℝ (∑ i, sz i) :=
        mem_unitaryCompact_of_mem_blockOrth (mul_mem (hτ θ) (bdK_mem_blockOrth κ))
      have f1 : torusElem L θ * y1 = lowerGL sz (scaleCoord sz ((n : ℝ) + 1)
          (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X)) *
            (torusElem L θ * bdK sz κ) := by
        rw [hy1, ← mul_assoc, mul_lowerGL (hτ θ), mul_assoc,
          adCoord_scaleCoord (hτ θ).1 (hτ θ).2 hs0]
      have f2 : torusElem L θ * y2 = lowerGL sz
          (adCoord (torusElem L θ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X) *
            (torusElem L θ * bdK sz κ) := by
        rw [hy2, ← mul_assoc, mul_lowerGL (hτ θ), mul_assoc]
      rw [f1, f2, norm_mul]
      refine le_trans ?_ (gramBound_mul_le t hs1 _)
      refine mul_le_mul (norm_expFun_le _ _ hk _ fun l _ => ?_)
        (norm_expFun_le _ _ hk _ fun l _ => rfl) (norm_nonneg _)
        (gramBound_nonneg _ _)
      ring
    rw [e1]
    refine (hC0 y1 y2).trans ?_
    rw [e2]
    calc C0 * ‖∫ θ, expFun (∑ i, sz i) (fun l => -t l) (torusElem L θ * y1) *
          expFun (∑ i, sz i) t (torusElem L θ * y2) ∂torusMeasure L.length‖ ≤
        C * ‖∫ θ, expFun (∑ i, sz i) (fun l => -t l) (torusElem L θ * y1) *
          expFun (∑ i, sz i) t (torusElem L θ * y2) ∂torusMeasure L.length‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ D X := mul_le_mul_of_nonneg_left
          (norm_integral_le_of_norm_le (hBθ X) (ae_of_all _ hpt)) (le_max_right _ _)
  -- the innermost limit
  have hlimθ : ∀ (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ),
      Tendsto (fun n : ℕ => Ψ n κ X) atTop (𝓝 (Ψ' κ X)) := by
    intro κ X
    obtain ⟨Mu, hMu⟩ := exists_bound_mul_tendsto huc (tendsto_lowerGL_scale X (bdK sz κ))
    obtain ⟨Mh, hMh⟩ := exists_bound_mul hhc (lowerGL sz X * bdK sz κ)
    have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 1 (one_mem _) 0)
    refine tendsto_integral_of_dominated_convergence (fun _ => Mu * Mh) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun θ => ?_) (ae_of_all _ fun θ => ?_)
    · exact ((hcont n).comp ((continuous_const.prodMk continuous_const).prodMk
        continuous_id)).aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_mul (hMu _ (hτK θ) n) (hMh _ (hτK θ)) (norm_nonneg _) hMu0
    · exact ((huc.tendsto _).comp (tendsto_const_nhds.mul
        (tendsto_lowerGL_scale X (bdK sz κ)))).mul_const _
  -- the middle limit
  have hlimX : ∀ κ : ∀ i, unitaryCompact ℝ (sz i),
      Tendsto (fun n : ℕ => ∫ X, Ψ n κ X) atTop (𝓝 (∫ X, Ψ' κ X)) := by
    intro κ
    refine tendsto_integral_of_dominated_convergence D (fun n => ?_) hDi
      (fun n => ae_of_all _ (hbound n κ)) (ae_of_all _ (hlimθ κ))
    exact AEStronglyMeasurable.integral_prod_right'
      (f := fun p : (Coord sz → ℝ) × (Fin L.length → ℝ) =>
        u (torusElem L p.2 * (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) p.1) * bdK sz κ)) *
          h (torusElem L p.2 * (lowerGL sz p.1 * bdK sz κ)))
      ((hcont n).comp ((continuous_const.prodMk continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable
  -- the outer limit
  have hlim : Tendsto (fun n : ℕ => ∫ κ, (∫ X, Ψ n κ X) ∂Measure.pi (fun i => haarK (sz i)))
      atTop (𝓝 (∫ κ, (∫ X, Ψ' κ X) ∂Measure.pi (fun i => haarK (sz i)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ X, D X) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun κ => ?_) (ae_of_all _ hlimX)
    · exact AEStronglyMeasurable.integral_prod_right'
        (f := fun q : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) => Ψ n q.1 q.2)
        (AEStronglyMeasurable.integral_prod_right'
          (f := fun q : ((∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ)) ×
            (Fin L.length → ℝ) =>
            u (torusElem L q.2 * (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) q.1.2) *
              bdK sz q.1.1)) * h (torusElem L q.2 * (lowerGL sz q.1.2 * bdK sz q.1.1)))
          (hcont n).aestronglyMeasurable)
    · exact norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound n κ))
  have e3 : ∀ (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ),
      coeffs (zeroModes L) (fun x => u (x * bdK sz κ) * h (x * (lowerGL sz X * bdK sz κ))) 1 =
        Ψ' κ X := by
    intro κ X
    rw [coeffs_eq_integral (F := fun x => u (x * bdK sz κ) * h (x * (lowerGL sz X * bdK sz κ)))
      ((huc.comp (continuous_id.mul continuous_const)).mul
        (hhc.comp (continuous_id.mul continuous_const))) L 1]
    simp only [mul_one, hΨ']
  simp_rw [e3]
  exact hlim

/-- **The limit along `Q`, value form.** Under the hypotheses of `RealLeviLimitStatement` on
`ds`, let `u, u'` be `O(N)`-finite functions of the principal series of the inverse characters
and `h, h'` `O(N)`-finite functions of the standard module of `ds`. If
`∫_{O(N)} u(κ d_s) h(κ) dκ = ∫_{O(N)} u'(κ d_s) h'(κ) dκ` for every `s > 0`, then the
torus-averaged limit pairings agree:
`∫_{K_M} ∫_X c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) dX dκ =
∫_{K_M} ∫_X c_Z(x ↦ u'(x diag(κ)) h'(x n̄(X) diag(κ))) dX dκ`. -/
theorem integral_coeffs_eq_of_eq (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement) {ds : List RealBlock}
    (hN : realRank ds = ∑ i, sz i)
    (hanti : ∀ p q : Fin (∑ i, sz i), p ≤ q →
      realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p)
    (hstrict : ∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p)
    {u h u' h' : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hh : h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
      (unitaryCompact ℝ (∑ i, sz i)))
    (hu' : u' ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hh' : h' ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
      (unitaryCompact ℝ (∑ i, sz i)))
    (h0 : ∀ (s : ℝ) (hs : 0 < s),
      ∫ κ, u ((κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) * scaleGL sz hs) * h κ
          ∂haarK (∑ i, sz i) =
        ∫ κ, u' ((κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) * scaleGL sz hs) * h' κ
          ∂haarK (∑ i, sz i)) :
    ∫ κ : (∀ i, unitaryCompact ℝ (sz i)),
        (∫ X : Coord sz → ℝ, coeffs (zeroModes (slots ds (∑ i, sz i)))
          (fun x => u (x * bdK sz κ) * h (x * (lowerGL sz X * bdK sz κ))) 1)
        ∂Measure.pi (fun i => haarK (sz i)) =
      ∫ κ : (∀ i, unitaryCompact ℝ (sz i)),
        (∫ X : Coord sz → ℝ, coeffs (zeroModes (slots ds (∑ i, sz i)))
          (fun x => u' (x * bdK sz κ) * h' (x * (lowerGL sz X * bdK sz κ))) 1)
        ∂Measure.pi (fun i => haarK (sz i)) := by
  obtain ⟨C, -, hI⟩ := exists_integral_torus_scale_eq hT1 hT3 c sz
  have hL := slots_cls_eq (sz := sz) hstrict
  have heq : ∀ n : ℕ,
      ∫ κ, (∫ X : Coord sz → ℝ, (∫ θ,
        u' (torusElem (slots ds (∑ i, sz i)) θ *
          (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) X) * bdK sz κ)) *
        h' (torusElem (slots ds (∑ i, sz i)) θ * (lowerGL sz X * bdK sz κ))
          ∂torusMeasure (slots ds (∑ i, sz i)).length))
        ∂Measure.pi (fun i => haarK (sz i)) =
      ∫ κ, (∫ X : Coord sz → ℝ, (∫ θ,
        u (torusElem (slots ds (∑ i, sz i)) θ *
          (lowerGL sz (scaleCoord sz ((n : ℝ) + 1) X) * bdK sz κ)) *
        h (torusElem (slots ds (∑ i, sz i)) θ * (lowerGL sz X * bdK sz κ))
          ∂torusMeasure (slots ds (∑ i, sz i)).length))
        ∂Measure.pi (fun i => haarK (sz i)) := by
    intro n
    have hs : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hI (isSignedPower ds) hu'.1 hh'.1.1 _ hL hs, hI (isSignedPower ds) hu.1 hh.1.1 _ hL hs,
      h0 _ hs]
  exact tendsto_nhds_unique (tendsto_integral_scale hT1 hN hanti hstrict hu hh)
    ((tendsto_integral_scale hT1 hN hanti hstrict hu' hh').congr heq)

end Limit

end RealParabolicLimitValue

end Langlands.Archimedean
