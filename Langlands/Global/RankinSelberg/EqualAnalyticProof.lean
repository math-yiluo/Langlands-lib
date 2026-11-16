import Langlands.Global.RankinSelberg.EqualAnalyticMain

/-! # Proof of the global analytic theory for equal-rank cuspidal pairs

Proof of `Langlands.Global.RankinSelbergGlobal.EqualAnalyticStatement` (Cogdell 2004,
Theorem 2.2). For cusp forms `φ`, `φ'` with central characters `ω`, `ω'` the product `P = φ φ'`
is continuous, invariant under `GL_n(F)`, transforms by `χ = ω ω'` under scalars and has chamber
decay in a Siegel decomposition; this is the data `EqualData`. Its main theorem gives the
continuation `I`, `Ĩ`, and `equalIntegral_unfold` (applied to `(χ, φ, φ', Φ)` and to
`(χ⁻¹, φ̃, φ̃', Φ̂)`) identifies the equal-rank integrals with the theta-kernel integrals for
`Re s` large.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global Langlands.Automorphic
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance proofEqSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance proofEqSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

theorem cuspFunction_zeta_mul {r : ℕ} (T : CuspidalOperatorRealization F r) (v : T.Space)
    {ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    (a : Points F 1) (g : Points F (r + 1)) :
    cuspFunction F T v (zeta F (r + 1) a * g) = ideleChar F ω a * cuspFunction F T v g := by
  have h2 := OperatorRealization.centralCharacter_evaluate T.realization ω hω v (ideleOf F a)
    (e F (r + 1) g)
  have h3 : AdelicGL.scalar F (r + 1) (ideleOf F a) * e F (r + 1) g =
      e F (r + 1) (zeta F (r + 1) a * g) := by
    show _ = e F (r + 1) ((e F (r + 1)).symm (AdelicGL.scalar F (r + 1) (ideleOf F a)) * g)
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  rw [h3] at h2
  rw [UnequalAnalytic.cuspFunction_eq]
  exact h2

theorem cuspFunction_symm {r : ℕ} (T : CuspidalOperatorRealization F r) (v : T.Space)
    (M : AdelicGL F (r + 1)) :
    cuspFunction F T v ((e F (r + 1)).symm M) =
      ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v) M := by
  rw [UnequalAnalytic.cuspFunction_eq]
  exact congrArg (ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v))
    ((e F (r + 1)).apply_symm_apply M)

omit [NumberField F] [CompactSpace (AdeleQuotient F)] in
theorem prod_decay_real {p₁ p₂ C₁ C₂ E A₁ A₂ S : ℝ} (hp₂ : 0 ≤ p₂)
    (h₁ : p₁ ≤ C₁ * E * Real.exp (A₁ * S)) (h₂ : p₂ ≤ C₂ * E * Real.exp (A₂ * S))
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    p₁ * p₂ ≤ |C₁| * |C₂| * E * Real.exp ((A₁ + A₂) * S) := by
  have h₁' : p₁ ≤ |C₁| * E * Real.exp (A₁ * S) :=
    h₁.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hE0)
      (Real.exp_pos _).le)
  have h₂' : p₂ ≤ |C₂| * E * Real.exp (A₂ * S) :=
    h₂.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hE0)
      (Real.exp_pos _).le)
  have e₁ := Real.exp_pos (A₁ * S)
  have e₂ := Real.exp_pos (A₂ * S)
  calc p₁ * p₂ ≤ (|C₁| * E * Real.exp (A₁ * S)) * (|C₂| * E * Real.exp (A₂ * S)) :=
        mul_le_mul h₁' h₂' hp₂ (by positivity)
    _ = |C₁| * |C₂| * (E * E) * (Real.exp (A₁ * S) * Real.exp (A₂ * S)) := by ring
    _ ≤ |C₁| * |C₂| * E * (Real.exp (A₁ * S) * Real.exp (A₂ * S)) := by
        gcongr
        nlinarith
    _ = |C₁| * |C₂| * E * Real.exp ((A₁ + A₂) * S) := by rw [add_mul, Real.exp_add]

/-- Chamber decay of the product of two cusp forms. -/
theorem pointDecay_cuspFunction_mul {r : ℕ} (T T' : CuspidalOperatorRealization F r) (v : T.Space)
    (v' : T'.Space) {Q₁ : Set (AdelicGL F (r + 1))} (hQ₁ : IsCompact Q₁) {K : ℝ} (hK : 0 ≤ K) :
    ∃ A₀ : ℝ, PointDecay Q₁ K (fun g => cuspFunction F T v g * cuspFunction F T' v' g) A₀ := by
  obtain ⟨A₁, hA₁, h₁⟩ := UnequalAnalytic.hasChamberDecay T.realization T.cuspidal v Q₁ hQ₁
    (K := K + 2) (by linarith)
  obtain ⟨A₂, hA₂, h₂⟩ := UnequalAnalytic.hasChamberDecay T'.realization T'.cuspidal v' Q₁ hQ₁
    (K := K + 2) (by linarith)
  refine ⟨A₁ + A₂, by positivity, fun c hc => ?_⟩
  obtain ⟨C₁, hC₁⟩ := h₁ c hc
  obtain ⟨C₂, hC₂⟩ := h₂ c hc
  refine ⟨|C₁| * |C₂|, fun x hx q hq => ?_⟩
  have b₁ : ‖ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v)
      (torusA (F := F) x * q)‖ ≤
      C₁ * Real.exp (-(c * spread x)) * Real.exp (A₁ * |∑ i, x i|) := hC₁ x hx q hq
  have b₂ : ‖ContinuousRationalFunctions.evaluate F (r + 1) (T'.realization.toContinuous v')
      (torusA (F := F) x * q)‖ ≤
      C₂ * Real.exp (-(c * spread x)) * Real.exp (A₂ * |∑ i, x i|) := hC₂ x hx q hq
  have hD : 0 ≤ spread x := Finset.sum_nonneg fun i _ => abs_nonneg _
  have e₁ : Real.exp (-(c * spread x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  beta_reduce
  rw [cuspFunction_symm, cuspFunction_symm, norm_mul]
  exact prod_decay_real (norm_nonneg _) b₁ b₂ (Real.exp_pos _).le e₁

omit [CompactSpace (AdeleQuotient F)] in
theorem ideleChar_inv_apply (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (a : Points F 1) :
    ideleChar F χ a⁻¹ = ideleChar F χ⁻¹ a := by
  rw [ideleChar_inv]
  have h := ideleChar_mul F χ a a⁻¹
  rw [mul_inv_cancel, ideleChar_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- **Cogdell 2004, Theorem 2.2.** -/
theorem equalAnalyticStatement_proof : EqualAnalyticStatement.{u} := by
  intro F _ _ _ r T T' ω ω' hω hω' ψ hψ v v' Φ hΦ φ φ' φdual φ'dual Φhat
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F (r + 1)
  obtain ⟨A₀, hPd⟩ := pointDecay_cuspFunction_mul T T' v v' hQ₁ hK
  have hφc : Continuous φ := UnequalAnalytic.continuous_cuspFunction F T v
  have hφ'c : Continuous φ' := UnequalAnalytic.continuous_cuspFunction F T' v'
  have hφr := UnequalAnalytic.cuspFunction_rational_mul F T v
  have hφ'r := UnequalAnalytic.cuspFunction_rational_mul F T' v'
  have hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      φ (zeta F (r + 1) a * g) * φ' (zeta F (r + 1) a * g) =
        ideleChar F (ω * ω') a * (φ g * φ' g) := by
    intro a g
    show cuspFunction F T v (zeta F (r + 1) a * g) * cuspFunction F T' v' (zeta F (r + 1) a * g) =
      _ * (cuspFunction F T v g * cuspFunction F T' v' g)
    rw [cuspFunction_zeta_mul T v hω, cuspFunction_zeta_mul T' v' hω', ideleChar_mul_char]
    ring
  let D : EqualData F r :=
    { χ := ω * ω'
      P := fun g => φ g * φ' g
      hPc := hφc.mul hφ'c
      hPr := fun c g => congrArg₂ (· * ·) (hφr c g) (hφ'r c g)
      hcent := hcent
      ψ := ψ
      hψ := hψ
      Φ := Φ
      hΦ := hΦ
      Q₁ := Q₁
      K := K
      hQ₁ := hQ₁
      hdec := hdec
      A₀ := A₀
      hPd := hPd }
  obtain ⟨σ₀, I, Idual, hconv, hpoles, hpolesd, hstrips, hFE⟩ := D.main
  refine ⟨σ₀, I, Idual, fun s hs => ?_, hpoles, hpolesd, hstrips, fun s _ => hFE s⟩
  obtain ⟨hfin, hfind, hIs, hIds⟩ := hconv s hs
  have hmain := equalIntegral_unfold F r (ω * ω') hφc hφ'c hφr hφ'r hcent
    (schwartzBruhat_properties F (r + 1) hΦ).1 s hfin
  -- the dual data
  have hdφ : φdual = fun g => φ (iota F (r + 1) g) :=
    funext fun g => UnequalAnalytic.dualFunction_eq F φ hφr g
  have hdφ' : φ'dual = fun g => φ' (iota F (r + 1) g) :=
    funext fun g => UnequalAnalytic.dualFunction_eq F φ' hφ'r g
  have hPd : (fun g => φdual g * φ'dual g) = D.Pd := by
    rw [hdφ, hdφ']
    rfl
  have hdc : Continuous φdual := hdφ ▸ hφc.comp (UnequalAnalytic.continuous_iota F (r + 1))
  have hd'c : Continuous φ'dual := hdφ' ▸ hφ'c.comp (UnequalAnalytic.continuous_iota F (r + 1))
  have hdr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      φdual (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = φdual g := by
    rw [hdφ]
    exact iota_rational_mul_invariant hφr
  have hd'r : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      φ'dual (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = φ'dual g := by
    rw [hdφ']
    exact iota_rational_mul_invariant hφ'r
  have hdcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
      φdual (zeta F (r + 1) a * g) * φ'dual (zeta F (r + 1) a * g) =
        ideleChar F (ω * ω')⁻¹ a * (φdual g * φ'dual g) := by
    intro a g
    rw [hdφ, hdφ']
    simp only
    rw [UnequalAnalytic.iota_mul, iota_zeta, hcent, ideleChar_inv_apply]
  have hdual := equalIntegral_unfold F r (ω * ω')⁻¹ hdc hd'c hdr hd'r hdcent
    D.hΦhc s (by rw [hPd]; exact hfind)
  have h2 := hdual.2
  rw [hPd] at h2
  exact ⟨hmain.1, hdual.1, hIs.trans hmain.2.symm, hIds.trans h2.symm⟩

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
