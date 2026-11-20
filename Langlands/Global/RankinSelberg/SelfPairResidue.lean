import Langlands.Global.RankinSelberg.EqualAnalyticPeriod
import Langlands.Global.RankinSelberg.EqualAnalyticSplitCentre
import Langlands.Global.RankinSelberg.SelfPairWhittaker
import Langlands.Global.RankinSelberg.SelfPairSchwartz

/-! # Nonzero residues for the equal-rank conjugate pair -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

namespace Langlands.Global.RankinSelbergGlobal.SelfPair

open Automorphic ContinuousRationalFunctions OperatorDeterminantSlice EqualAnalytic
open NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj NNReal ComplexConjugate

local instance selfResidueSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance selfResidueSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- A test standard outside the prescribed finite set can be chosen with both origin
evaluations nonzero. -/
theorem exists_schwartzBruhat_origin_ne_zero (n : ℕ) (S : Finset (FinitePlace F))
    (ψ : AddChar (Adeles F) ℂ) :
    ∃ Φ ∈ schwartzBruhat F n, IsStandardOutside F n S Φ ∧
      Φ 0 ≠ 0 ∧ fourierTransform F n ψ Φ 0 ≠ 0 := by
  have hzero : (0 : RowVector F n) ∈ integralOutside F n S := by
    intro v _ j
    simpa only [localCoordinates, Matrix.zero_apply, map_zero] using
      (v.adicCompletionIntegers F).zero_mem
  obtain ⟨φ, hφ, hstd, hnn, hφ0⟩ := exists_nonnegative_standardSchwartz_of_mem hzero
  refine ⟨fun x => (φ x : ℂ), hφ, hstd, Complex.ofReal_ne_zero.mpr (hφ0.trans_ne one_ne_zero), ?_⟩
  obtain ⟨hc, hint, _⟩ := schwartzBruhat_properties F n hφ
  have hφc : Continuous φ := by
    simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp hc
  have hφint : Integrable φ (rectangleMeasure F 1 n) := by
    have hre := hint.re
    change Integrable (fun x => (φ x : ℂ).re) (rectangleMeasure F 1 n) at hre
    simpa only [Complex.ofReal_re] using hre
  have hpos := integral_pos_of_integrable_nonneg_nonzero hφc hφint hnn
    (hφ0.trans_ne one_ne_zero)
  simp only [fourierTransform, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    AddChar.map_zero_eq_one, mul_one, integral_complex_ofReal]
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

variable {r : ℕ}

/-- Conjugation preserves triviality on the positive archimedean split centre. -/
theorem isTrivialOnSplitCentre_conjugate (T : CuspidalOperatorRealization F r)
    (hT : CuspidalPairPoles.IsTrivialOnSplitCentre T) :
    CuspidalPairPoles.IsTrivialOnSplitCentre T.conjugate := by
  intro a ha w x
  obtain ⟨v, rfl⟩ := T.conjugateEquiv.surjective w
  change evaluate F (r + 1) (T.conjugate.realization.toContinuous (T.conjugateEquiv v))
    (AdelicGL.scalar F (r + 1) a * x) = _
  rw [T.toContinuous_conjugateEquiv, evaluate_continuousConj, evaluate_continuousConj,
    hT a ha v x]

/-- Pairing a nonzero cusp form with its pointwise conjugate gives a positive period. -/
theorem residueConstant_conjugate_pos (T : CuspidalOperatorRealization F r)
    {ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    (f : T.Space) (hf : f ≠ 0) :
    0 < (residueConstant F r (fun x =>
      cuspFunction F T.conjugate (T.conjugateEquiv f) x * cuspFunction F T f x) 0).re := by
  let n := r + 1
  let Q := OperatorDeterminantSlice.Quotient F n
  let ν := residueSlabMeasure F n
  let A := toQuotient F n T.realization f
  let H (q : Q) := ‖A q‖ ^ 2
  have hA2 : MemLp A 2 ν := by
    apply (memLp_supNorm_residueSlab F n T.realization T.cuspidal 0 f).mono'
      A.continuous.aestronglyMeasurable
    filter_upwards [] with q
    simpa only [curve_zero, translate_one, A] using
      norm_le_supNorm F n T.realization 0 f q (s := 0) ⟨by norm_num, by norm_num⟩
  have hH : Integrable H ν := by
    have heq : H = (fun q => ‖A q‖) * (fun q => ‖A q‖) := funext fun q => pow_two _
    rw [heq]
    exact hA2.norm.integrable_mul hA2.norm
  have hHc : Continuous H := A.continuous.norm.pow 2
  have hA_ne : A ≠ 0 := by
    intro heq
    apply hf
    apply toQuotient_injective F n T.realization
    rw [map_zero]
    exact heq
  obtain ⟨x, hx⟩ : ∃ x : AdelicGL F n, evaluate F n (T.realization.toContinuous f) x ≠ 0 := by
    by_contra! h
    apply hA_ne
    ext q
    obtain ⟨x, rfl⟩ := point_surjective F n q
    simpa only [A, toQuotient_point, ContinuousMap.zero_apply] using h x
  let d (q : Q) : ℝ := ((quotientDeterminantNorm F n q : ℝ≥0) : ℝ)
  have hdc : Continuous d := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (quotientDeterminantNorm F n).continuous)
  let U := d ⁻¹' Ioo 1 (Real.exp n) ∩ Function.support H
  have hU : IsOpen U := (isOpen_Ioo.preimage hdc).inter hHc.isOpen_support
  let t := expUnit ((n : ℝ) / 2)
  obtain ⟨z, hz⟩ := exists_scalar_determinantNorm F n (Nat.succ_ne_zero r)
    (t * (AdelicBlockDeterminantCharacter.determinantNorm F n x)⁻¹)
  let y := AdelicGL.scalar F n z * x
  have hy : AdelicBlockDeterminantCharacter.determinantNorm F n y = t := by
    simp only [y, map_mul, hz, inv_mul_cancel_right]
  have hd : d (point F n y) = Real.exp ((n : ℝ) / 2) := by
    simp only [d, quotientDeterminantNorm_point, hy, t, coe_expUnit]
  have hyne : A (point F n y) ≠ 0 := by
    rw [show A = _ from rfl, toQuotient_point, show y = _ from rfl,
      T.realization.centralCharacter_evaluate ω hω]
    exact mul_ne_zero (Units.ne_zero _) hx
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.succ_pos r)
  have hyU : point F n y ∈ U := by
    refine ⟨?_, pow_ne_zero 2 (norm_ne_zero_iff.mpr hyne)⟩
    change 1 < d (point F n y) ∧ d (point F n y) < Real.exp n
    rw [hd]
    refine ⟨?_, Real.exp_lt_exp.mpr (by linarith)⟩
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hsubset : U ⊆ Function.support H ∩ determinantSlab F n 1 (Real.exp n) := by
    intro q hq
    obtain ⟨g, rfl⟩ := point_surjective F n q
    refine ⟨hq.2, ?_⟩
    let e := GeneralLinearGroupPoints.adelicHomeomorph F n
    have hdet : detNorm F n (e.symm g) = d (point F n g) := by
      change absDet F n (e (e.symm g)) = _
      rw [e.apply_symm_apply]
      simp only [d, quotientDeterminantNorm_point]
      rfl
    refine ⟨e.symm g, ?_, rfl⟩
    change 1 ≤ detNorm F n (e.symm g) ∧ detNorm F n (e.symm g) < Real.exp n
    rw [hdet]
    exact ⟨hq.1.1.le, hq.1.2⟩
  have hpos : 0 < ∫ q, H q ∂ν := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun q => sq_nonneg ‖A q‖) hH).2
    exact (hU.measure_pos (quotientHaarMeasure F n) ⟨_, hyU⟩).trans_le (measure_mono hsubset)
  have hconj (q : Q) : toQuotient F n T.conjugate.realization (T.conjugateEquiv f) q =
      conj (A q) := by
    obtain ⟨g, rfl⟩ := point_surjective F n q
    simp only [A, toQuotient_point, T.toContinuous_conjugateEquiv]
    exact evaluate_continuousConj F (r + 1) _ g
  rw [← residuePairing_eq_residueConstant F T.conjugate T]
  change 0 < (∫ q, toQuotient F n T.conjugate.realization (T.conjugateEquiv f) q * A q ∂ν).re
  have heq : (fun q => toQuotient F n T.conjugate.realization (T.conjugateEquiv f) q * A q) =
      fun q => (H q : ℂ) := by
    funext q
    rw [hconj, mul_comm, Complex.mul_conj', Complex.ofReal_pow]
  rw [heq, integral_complex_ofReal, Complex.ofReal_re]
  exact hpos

private theorem conjugate_product_character (T : CuspidalOperatorRealization F r)
    (hT : CuspidalPairPoles.IsTrivialOnSplitCentre T)
    {ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω) :
    ∀ z, ideleChar F (conjCharacter F ω * ω) z = 1 := by
  obtain ⟨χ, hχu, hχ⟩ := cuspidalSplitCentreUnitaryCentralCharacter F r T hT
  have h : χ = ω := (T.realization.existsUnique_hasCentralCharacter T.irreducible).unique hχ hω
  subst χ
  intro z
  rw [mul_comm (conjCharacter F ω) ω, mul_conjCharacter_eq_one ω hχu]
  rfl

/-- The actual conjugate realization is a contragredient of the original split-centre
cuspidal realization, as witnessed by its nonzero residue pairing. -/
theorem conjugate_isContragredientOf_of_splitCentre (T : CuspidalOperatorRealization F r)
    (hT : CuspidalPairPoles.IsTrivialOnSplitCentre T) :
    T.conjugate.realization.IsContragredientOf T.realization := by
  obtain ⟨ω, hω, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  obtain ⟨f, x, hx⟩ := T.realization.exists_evaluate_ne_zero T.irreducible
  have hf : f ≠ 0 := by
    intro h
    apply hx
    rw [h, map_zero]
    rfl
  have hpos := residueConstant_conjugate_pos T hω f hf
  refine isContragredientOf_of_residueConstant_ne_zero F T.conjugate T
    (OperatorRealization.HasCentralCharacter.conjugate T.realization hω) hω
    (conjugate_product_character T hT hω) (T.conjugateEquiv f) f ?_
  intro heq
  rw [heq, Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

/-- In the conjugate self-pair, any nonzero vector and test function with both origin
values nonzero give an equal-rank global integral with simple poles at 0 and 1. -/
def SelfPairIntegralPoleStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r),
    CuspidalPairPoles.IsTrivialOnSplitCentre T →
    ∀ (ω : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ), T.realization.HasCentralCharacter ω →
    ∀ (ψ : AddChar (Adeles K) ℂ), IsStandardAdditiveCharacter K ψ →
    ∀ (v : T.Space), v ≠ 0 →
    ∀ Φ ∈ schwartzBruhat K (r + 1), Φ 0 ≠ 0 →
      fourierTransform K (r + 1) ψ Φ 0 ≠ 0 →
    let φ := cuspFunction K T.conjugate (T.conjugateEquiv v)
    let φ' := cuspFunction K T v
    let χ := conjCharacter K ω * ω
    ∃ σ : ℝ, ∃ I : ℂ → ℂ,
      (∀ s : ℂ, σ < s.re →
        Integrable (equalIntegrand K χ φ φ' Φ s) (centralQuotientMeasure K (r + 1)) ∧
        I s = equalIntegral K χ φ φ' Φ s) ∧
      CuspidalPairPoles.IsBoundedInVerticalStrips I ∧
      CuspidalPairPoles.HasSimplePoleProfile I True

/-- The explicitly computed residues are nonzero for the conjugate self-pair. -/
theorem selfPairIntegralPole : SelfPairIntegralPoleStatement.{u} := by
  intro K _ _ _ r T hT ω hω ψ hψ v hv Φ hΦ hΦ₀ hΦh₀ φ φ' χ
  obtain ⟨σ, I, hI, hstrip, hprofile⟩ := equalIntegral_splitCentre_continuation T.conjugate T
    (isTrivialOnSplitCentre_conjugate T hT) hT
    (OperatorRealization.HasCentralCharacter.conjugate T.realization hω) hω
    ψ hψ (T.conjugateEquiv v) v Φ hΦ
  have hres := residueConstant_conjugate_pos T hω v hv
  have hres₀ : residueConstant K r (fun x => φ x * φ' x) 0 ≠ 0 := by
    intro heq
    change 0 < (residueConstant K r (fun x => φ x * φ' x) 0).re at hres
    rw [heq, Complex.zero_re] at hres
    exact (lt_irrefl 0) hres
  refine ⟨σ, I, hI, hstrip, hprofile.1, ?_⟩
  intro p hp
  obtain ⟨hm, hlo, horder⟩ := hprofile.2 p hp
  refine ⟨hm, hlo, iff_true_intro (horder.mpr ⟨conjugate_product_character T hT hω, hres₀, ?_⟩)⟩
  by_cases h : p = 0
  · simpa only [h, ite_true] using hΦ₀
  · simpa only [h, ite_false] using hΦh₀

end Langlands.Global.RankinSelbergGlobal.SelfPair
