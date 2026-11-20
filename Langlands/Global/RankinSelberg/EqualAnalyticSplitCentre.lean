import Langlands.Global.RankinSelberg.EqualAnalyticProof
import Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof

/-! # Residue coefficients of the split-centre equal-rank integral -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open NumberField MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Automorphic CuspidalPairPoles

local instance splitSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance splitSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

/-- The norm section used in the central integral is a positive archimedean scalar. -/
theorem ideleOf_normScale (y : ℝ) :
    ideleOf F (normScale F y) =
      PositiveRealIdeles.full F (expUnit (y / Module.finrank ℚ F)) := by
  change AdelicGL.determinant F 1 (GeneralLinearGroupPoints.adelicHomeomorph F 1
    (normScale F y)) = _
  rw [normScale, ContinuousMulEquiv.apply_symm_apply, determinant_ofInfinite_torInf,
    Fin.sum_univ_one]

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- Evaluating a nonzero cuspidal vector shows that its central character is trivial
on the norm section when the realization is trivial on the split centre. -/
theorem ideleChar_normScale_of_trivial (T : CuspidalOperatorRealization F r)
    (hT : IsTrivialOnSplitCentre T) {ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hω : T.realization.HasCentralCharacter ω) (y : ℝ) :
    ideleChar F ω (normScale F y) = 1 := by
  obtain ⟨f, x, hx⟩ := T.realization.exists_evaluate_ne_zero T.irreducible
  have ha : IsPositiveArchimedeanScalar (ideleOf F (normScale F y)) := by
    rw [ideleOf_normScale]
    exact isPositiveArchimedeanScalar_positiveRealIdeles _
  have h := T.realization.centralCharacter_evaluate ω hω f (ideleOf F (normScale F y)) x
  rw [hT _ ha f x] at h
  exact mul_right_cancel₀ hx (h.symm.trans (one_mul _).symm)

omit [CompactSpace (AdeleQuotient F)] in
private theorem normPower_exponent_eq_zero {χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hχ : ∀ y, ideleChar F χ (normScale F y) = 1) {w : ℂ}
    (hw : ∀ a, ideleChar F χ a = detPower F 1 a w) : w = 0 := by
  have hconst : (fun y : ℝ => Complex.exp (w * y)) = fun _ => (1 : ℂ) := by
    funext y
    specialize hw (normScale F y)
    rwa [hχ, detPower_one_eq, logNorm, detNorm_normScale, Real.log_exp, eq_comm] at hw
  have hd : HasDerivAt (fun y : ℝ => Complex.exp (w * y)) w 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul w).cexp
    simpa only [id_eq, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_mul] using h
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))

omit [Field F] [NumberField F] in
private theorem neg_one_lt_zero_withTop : (-1 : WithTop ℤ) < 0 := by
  change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
  exact WithTop.coe_lt_coe.2 (by decide)

omit [Field F] [NumberField F] in
private theorem order_entire_add_simple {G : ℂ → ℂ} {a p : ℂ} (hG : AnalyticAt ℂ G p) :
    MeromorphicAt (fun s => G s + a / (s - p)) p ∧
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => G s + a / (s - p)) p ∧
      (meromorphicOrderAt (fun s => G s + a / (s - p)) p < 0 ↔ a ≠ 0) := by
  by_cases ha : a = 0
  · simp only [ha, zero_div, add_zero, ne_self_iff_false, iff_false, not_lt]
    exact ⟨hG.meromorphicAt, neg_one_lt_zero_withTop.le.trans hG.meromorphicOrderAt_nonneg,
      hG.meromorphicOrderAt_nonneg⟩
  have hfrac : MeromorphicAt (fun s : ℂ => a / (s - p)) p :=
    analyticAt_const.meromorphicAt.div
      (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hord : meromorphicOrderAt (fun s : ℂ => a / (s - p)) p = (-1 : ℤ) := by
    refine (meromorphicOrderAt_eq_int_iff hfrac).2 ⟨fun _ => a, analyticAt_const, ha, ?_⟩
    exact Eventually.of_forall fun s => by rw [zpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hlt : meromorphicOrderAt (fun s : ℂ => a / (s - p)) p < meromorphicOrderAt G p := by
    rw [hord]
    exact neg_one_lt_zero_withTop.trans_le hG.meromorphicOrderAt_nonneg
  have horder := meromorphicOrderAt_add_eq_right_of_lt hG.meromorphicAt hlt
  change meromorphicOrderAt (fun s => G s + a / (s - p)) p = _ at horder
  rw [hord] at horder
  rw [horder]
  exact ⟨hG.meromorphicAt.add hfrac, le_rfl, iff_of_true neg_one_lt_zero_withTop ha⟩

omit [Field F] [NumberField F] in
private theorem orders_two_fractions {G : ℂ → ℂ} (hG : Differentiable ℂ G) (a b : ℂ) :
    let I (s : ℂ) := G s + a / (s - 0) + b / (s - 1)
    DifferentiableOn ℂ I ({0, 1} : Set ℂ)ᶜ ∧
      ∀ p ∈ ({0, 1} : Set ℂ), MeromorphicAt I p ∧
        (-1 : WithTop ℤ) ≤ meromorphicOrderAt I p ∧
        (meromorphicOrderAt I p < 0 ↔ (if p = 0 then a else b) ≠ 0) := by
  intro I
  have hd := hasAtMostSimplePolesIn_two hG (a₁ := a) (a₂ := b) (m := 1)
    (b₁ := 0) (b₂ := -1) (by norm_num) (P := {0, 1}) (by simp) (by simp)
  refine ⟨by simpa only [I, one_mul, sub_eq_add_neg, neg_zero, add_zero] using hd.1, ?_⟩
  intro p hp
  rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp : p = 0 ∨ p = 1) with rfl | rfl
  · have hreg : AnalyticAt ℂ (fun s => G s + b / (s - 1)) 0 :=
      (hG.analyticAt _).add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num))
    have hI : I = fun s => (G s + b / (s - 1)) + a / (s - 0) := by
      funext s
      simp only [I]
      ac_rfl
    rw [hI]
    simpa using order_entire_add_simple (a := a) hreg
  · have hreg : AnalyticAt ℂ (fun s => G s + a / (s - 0)) 1 :=
      (hG.analyticAt _).add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num))
    simpa [I] using order_entire_add_simple (a := b) hreg

/-- An equal-rank integral is holomorphic off `0, 1`, with at most simple
poles there. Each pole requires the trivial product character, a nonzero
cuspidal period, and the corresponding nonzero test value at the origin. -/
def HasSplitCentreResidueProfile (I : ℂ → ℂ) (trivialCentralCharacter : Prop)
    (period testAtZero fourierAtZero : ℂ) : Prop :=
  DifferentiableOn ℂ I ({0, 1} : Set ℂ)ᶜ ∧
    ∀ p ∈ ({0, 1} : Set ℂ), MeromorphicAt I p ∧
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt I p ∧
      (meromorphicOrderAt I p < 0 ↔
        trivialCentralCharacter ∧ period ≠ 0 ∧
          (if p = 0 then testAtZero else fourierAtZero) ≠ 0)

namespace EqualData

variable (D : EqualData F r)

/-- The explicit split-centre continuation of the theta-kernel integral, with the pole
at each distinguished point detected by its own residue coefficient. -/
theorem splitCentre_continuation (hχ : ∀ y, ideleChar F D.χ (normScale F y) = 1) :
    ∃ σ : ℝ, ∃ I : ℂ → ℂ,
      (∀ s : ℂ, σ < s.re →
        (∫⁻ x, thetaKernelNorm F r D.P D.Φ s (Quotient.out x) ∂μq (F := F) (r := r)) < ⊤ ∧
        I s = ∫ x, thetaKernel F r D.P D.Φ s (Quotient.out x) ∂μq (F := F) (r := r)) ∧
      IsBoundedInVerticalStrips I ∧
      HasSplitCentreResidueProfile I (∀ z, ideleChar F D.χ z = 1)
        (residueConstant F r D.P 0) (D.Φ 0) (D.Φh 0) := by
  let G : ℂ → ℂ := fun s => D.A s + D.At (1 - s)
  rcases ideleChar_dichotomy F D.χ with ⟨w, hw⟩ | ⟨z₀, hz₀, hnz₀⟩
  · have hzero := normPower_exponent_eq_zero hχ hw
    subst w
    have htriv : ∀ z, ideleChar F D.χ z = 1 := by
      intro z
      rw [hw, detPower_one_eq, zero_mul, Complex.exp_zero]
    let C := residueConstant F r D.P 0
    let n : ℂ := ((r + 1 : ℕ) : ℂ)
    have hn : n ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)
    let a := -(D.Φ 0 * C) / n
    let b := (D.Φh 0 * C) / n
    let I (s : ℂ) := G s + a / (s - 0) + b / (s - 1)
    have hI (s : ℂ) : I s = G s + D.Φh 0 * (C / (n * (s - 1))) - D.Φ 0 * (C / (n * s)) := by
      simp only [I, a, b, div_div, mul_div_assoc, neg_div, sub_eq_add_neg, neg_zero, add_zero]
      ring
    obtain ⟨hd, horder⟩ := orders_two_fractions D.differentiable_G a b
    have hstrip := boundedInVerticalStripsAwayFrom_two D.bounded_G (a₁ := a) (a₂ := b)
      (m := 1) (b₁ := 0) (b₂ := -1) (by norm_num) (P := {0, 1}) (by simp) (by simp)
    refine ⟨D.σ₀ 0, I, ?_, ?_, hd, ?_⟩
    · intro s hs
      obtain ⟨hfin, _, hlt₁, hlt₂, _, _, hpos₁, hpos₂, _, _⟩ := D.conditions 0 s hs
      refine ⟨D.lintegral_kernel_lt_top hfin, ?_⟩
      rw [D.integral_kernel_eq s (D.integrable_resLt hlt₁) (D.integrable_resLt hlt₂),
        residueLt_eq_of_char D.hPc D.hPr D.hcent hw hpos₁ (D.integrable_resLt hlt₁),
        residueLt_eq_of_char D.hPc D.hPr D.hcent hw hpos₂ (D.integrable_resLt hlt₂), hI]
      simp only [G, add_zero, C, n]
    · intro lo hi ε hε
      by_cases hle : lo ≤ hi
      · obtain ⟨M, _, hM⟩ := hstrip lo hi hle ε hε
        exact ⟨M, fun s hlo hhi hs₀ hs₁ => by
          simpa only [I, G, one_mul, sub_eq_add_neg, neg_zero, add_zero] using
            hM s hlo hhi (fun p hp => by
              rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp :
                p = 0 ∨ p = 1) with rfl | rfl
              · simpa only [sub_zero] using hs₀
              · exact hs₁)⟩
      · exact ⟨0, fun _ hlo hhi _ _ => (hle (hlo.trans hhi)).elim⟩
    · intro p hp
      obtain ⟨hm, hge, hl⟩ := horder p hp
      refine ⟨hm, hge, hl.trans ?_⟩
      have hcoeff : (if p = 0 then a else b) ≠ 0 ↔
          residueConstant F r D.P 0 ≠ 0 ∧ (if p = 0 then D.Φ 0 else D.Φh 0) ≠ 0 := by
        by_cases hp₀ : p = 0 <;> simp [hp₀, a, b, hn, C, and_comm]
      exact hcoeff.trans ⟨fun h => ⟨htriv, h⟩, fun h => h.2⟩
  · refine ⟨D.σ₀ 0, G, ?_, ?_, D.differentiable_G.differentiableOn, ?_⟩
    · intro s hs
      obtain ⟨hfin, _, hlt₁, hlt₂, _, _, _, _, _, _⟩ := D.conditions 0 s hs
      refine ⟨D.lintegral_kernel_lt_top hfin, ?_⟩
      rw [D.integral_kernel_eq s (D.integrable_resLt hlt₁) (D.integrable_resLt hlt₂),
        residueLt_eq_zero D.hPc D.hPr D.hcent hz₀ hnz₀ _ (D.integrable_resLt hlt₁),
        residueLt_eq_zero D.hPc D.hPr D.hcent hz₀ hnz₀ _ (D.integrable_resLt hlt₂)]
      simp [G]
    · intro lo hi ε hε
      obtain ⟨M, _, hM⟩ := D.bounded_G lo hi
      exact ⟨M, fun s hlo hhi _ _ => hM s hlo hhi⟩
    · intro p _
      have h := D.differentiable_G.analyticAt p
      refine ⟨h.meromorphicAt, neg_one_lt_zero_withTop.le.trans h.meromorphicOrderAt_nonneg, ?_⟩
      exact ⟨fun ho => (not_lt_of_ge h.meromorphicOrderAt_nonneg ho).elim,
        fun htriv => (hnz₀ (htriv.1 z₀)).elim⟩

end EqualData

/-- The regularized equal-rank integral with its two residues recorded in terms
of the determinant-slab period of the two cusp forms. -/
theorem equalIntegral_splitCentre_continuation
    (T T' : CuspidalOperatorRealization F r) (hT : IsTrivialOnSplitCentre T)
    (hT' : IsTrivialOnSplitCentre T')
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hω : T.realization.HasCentralCharacter ω) (hω' : T'.realization.HasCentralCharacter ω')
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (v : T.Space) (v' : T'.Space) (Φ : RowVector F (r + 1) → ℂ)
    (hΦ : Φ ∈ schwartzBruhat F (r + 1)) :
    let φ := cuspFunction F T v
    let φ' := cuspFunction F T' v'
    ∃ σ : ℝ, ∃ I : ℂ → ℂ,
      (∀ s : ℂ, σ < s.re →
        Integrable (equalIntegrand F (ω * ω') φ φ' Φ s) (centralQuotientMeasure F (r + 1)) ∧
        I s = equalIntegral F (ω * ω') φ φ' Φ s) ∧
      IsBoundedInVerticalStrips I ∧
      HasSplitCentreResidueProfile I (∀ z, ideleChar F (ω * ω') z = 1)
        (residueConstant F r (fun g => φ g * φ' g) 0) (Φ 0)
        (fourierTransform F (r + 1) ψ Φ 0) := by
  intro φ φ'
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F (r + 1)
  obtain ⟨A₀, hPd⟩ := pointDecay_cuspFunction_mul T T' v v' hQ₁ hK
  have hφc : Continuous φ := UnequalAnalytic.continuous_cuspFunction F T v
  have hφ'c : Continuous φ' := UnequalAnalytic.continuous_cuspFunction F T' v'
  have hφr := UnequalAnalytic.cuspFunction_rational_mul F T v
  have hφ'r := UnequalAnalytic.cuspFunction_rational_mul F T' v'
  have hcent (a : Points F 1) (g : Points F (r + 1)) :
      φ (zeta F (r + 1) a * g) * φ' (zeta F (r + 1) a * g) =
        ideleChar F (ω * ω') a * (φ g * φ' g) := by
    change cuspFunction F T v (zeta F (r + 1) a * g) *
      cuspFunction F T' v' (zeta F (r + 1) a * g) = _
    rw [cuspFunction_zeta_mul T v hω, cuspFunction_zeta_mul T' v' hω', ideleChar_mul_char]
    dsimp only [φ, φ']
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
  have hχ (y : ℝ) : ideleChar F D.χ (normScale F y) = 1 := by
    change ideleChar F (ω * ω') (normScale F y) = 1
    rw [ideleChar_mul_char, ideleChar_normScale_of_trivial T hT hω,
      ideleChar_normScale_of_trivial T' hT' hω', one_mul]
  obtain ⟨σ, I, hI, hbound, hp⟩ := D.splitCentre_continuation hχ
  refine ⟨σ, I, ?_, hbound, hp⟩
  intro s hs
  obtain ⟨hfin, hIs⟩ := hI s hs
  obtain ⟨hint, heq⟩ := equalIntegral_unfold F r (ω * ω') hφc hφ'c hφr hφ'r hcent D.hΦc s hfin
  exact ⟨hint, hIs.trans heq.symm⟩

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
