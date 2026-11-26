import Langlands.Global.RankinSelberg.RealAdjacentCanonicalChamber
import Langlands.Global.RankinSelberg.RealOrthogonalCompactProjection
import Langlands.Global.RankinSelberg.RealLocalEqualShiftedProducts

/-! # Square reflection at a fixed real Whittaker evaluation point -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapSquareReflection

open ArchimedeanLocal
open Langlands.Archimedean (unitaryCompact realRank_map_character)
open Langlands.GeneralLinear (inverseTranspose)
open RealGodement (realRectangularSchwartzFourier realWeightedMatrixTest realCompactMatrixTranslate
  realWeightedMatrixTest_reproduce exists_realCompactMatrixWeight realLocalCompactFourierWeight
  realRectangularSchwartzFourier_apply norm_determinantWeight_real continuous_determinantWeight)
open RealJacquet (realAdjacentMatrixWeight detCharacter realAdjacentSquareGrowth
  realLocalCompactProjectionReduction realCompactMatrixTranslate_inverse_of_mem
  realOrthogonalCompactProjectionPremise inverseTranspose_orthogonal splitModel_growth
  HasRealPairNormalizedGrowth realMatrixHeight_inverseTranspose)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable (t : ℕ)

local notation "H" => Langlands.GeneralLinear (t + 1) ℝ
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ
local notation "O" => Matrix.unitaryGroup (Fin (t + 1)) ℝ
local notation "ι" => inverseTranspose (t + 1) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

private theorem determinantWeight_eq {n : ℕ} (c : RealCharacterData) (s : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    RealGodement.determinantWeight c s g = detCharacter c.character.toMonoidHom g * P g s := by
  change (c.character (Langlands.GeneralLinear.determinant g) : ℂ) * ((|g.val.det| : ℝ) : ℂ) ^ s = _
  unfold detCharacter ArchimedeanLocal.detPower realNormalizedAbs
  have hg : g.val.det ≠ 0 := (Langlands.GeneralLinear.determinant g).ne_zero
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hg)),
    ← Complex.ofReal_log (abs_nonneg _), mul_comm (Real.log _ : ℂ)]
  rfl

/-- The square weight of the adjacent expansion is the weighted square test at the shifted
exponent. -/
theorem matrixWeight_eq_weightedTest (c : RealCharacterData) (Φ : M → ℂ) (s : ℂ) (y : H) :
    realAdjacentMatrixWeight c.character.toMonoidHom Φ s y =
      realWeightedMatrixTest c Φ (s + (t : ℂ) / 2) y := by
  unfold realAdjacentMatrixWeight realWeightedMatrixTest
  rw [determinantWeight_eq, mul_assoc]

/-- The compact averaging kernel of a weighted square test against a function of polynomial
height growth is integrable once the determinant exponent is large. -/
theorem integrable_compactInsertion {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure H) [μ.IsHaarMeasure] (ν : Measure K) [IsFiniteMeasure ν]
    (iK : K →* H) (hι : Continuous iK) (κ : K → ℂ) (hκ : Continuous κ)
    (d : RealCharacterData) (Ψ : 𝓢(M, ℂ)) {V : H → ℂ} (hVc : Continuous V)
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hV : ∀ g, ‖V g‖ ≤ C * realMatrixHeight g ^ N)
    (w : ℂ) (hw : (t : ℝ) + 1 + 2 * N ≤ d.exponent.re + w.re) (x : H) :
    Integrable (fun p : K × H =>
      κ p.1 * realWeightedMatrixTest d Ψ w (iK p.1⁻¹ * p.2) * V (x * p.2)) (ν.prod μ) := by
  let A := realWeightedMatrixTest d Ψ w
  let E (g : H) : ℝ := realMatrixHeight g
  have hE : Continuous E := continuous_realMatrixHeight
  have hE0 (g : H) : 0 ≤ E g := RealPlaceRestriction.realMatrixHeight_nonneg g
  have hA : Continuous A :=
    (Ψ.continuous.comp Units.continuous_val).mul (continuous_determinantWeight d w)
  refine (ComplexJacquet.integrable_compact_average_iff iK hι.measurable ν μ κ A
    (fun g => V (x * g))).mpr ?_
  let T (k : K) := C * E (x * iK k) ^ N * ‖κ k‖
  have hT : Continuous T :=
    (((hE.comp (continuous_const.mul hι)).pow N).const_mul C).mul hκ.norm
  have hTi : Integrable T ν :=
    hT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace T)
  let B (g : H) := E g ^ N * ‖A g‖
  have hB : Integrable B μ := by
    have h := Langlands.GodementJacquet.integrable_realMatrixWeightedNorm (r := t) μ
      (f := fun g : H => ((E g ^ N : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp (hE.pow N)).measurable Ψ (C := 1) zero_le_one
      (fun g => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hE0 g) N), one_mul])
      (q := d.exponent.re + w.re) (by linarith)
    refine h.congr (ae_of_all _ fun g => ?_)
    simp only [B, A, realWeightedMatrixTest, norm_mul, norm_determinantWeight_real, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hE0 g) N)]
    ring
  refine (hTi.mul_prod hB).mono'
    ((hA.comp continuous_snd).mul ((hκ.comp continuous_fst).mul
      (hVc.comp (continuous_const.mul ((hι.comp continuous_fst).mul
        continuous_snd))))).aestronglyMeasurable
    (ae_of_all _ ?_)
  rintro ⟨k, g⟩
  have hH : E (x * (iK k * g)) ≤ E (x * iK k) * E g := by
    rw [← mul_assoc]
    exact realMatrixHeight_mul_le _ _
  have hP : ‖V (x * (iK k * g))‖ ≤ C * (E (x * iK k) ^ N * E g ^ N) := by
    rw [← mul_pow]
    exact (hV _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hE0 _) hH N) hC)
  simp only [norm_mul]
  calc
    ‖A g‖ * (‖κ k‖ * ‖V (x * (iK k * g))‖) ≤
        ‖A g‖ * (‖κ k‖ * (C * (E (x * iK k) ^ N * E g ^ N))) := by gcongr
    _ = T k * B g := by simp only [T, B]; ring

/-- The square pair at a fixed evaluation point of a uniform Whittaker value has the
adjoining-character normalization, with exponential growth on vertical strips. -/
def RealGapSquareReflectionStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (c : RealCharacterData) (fs : List RealCharacterData),
    fs.length = t + 1 →
  ∀ (Φ : 𝓢(M, ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : O => fun X : M =>
      Φ ((((Unitary.toUnits k : H))⁻¹).val * X))) →
  ∀ (B : Automorphic.realStandardKFinite (t + 1) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
    IsRealUniformWhittakerIntertwiner t (fs.map RealBlock.character) a B →
  ∀ (f : Automorphic.realStandardKFinite (t + 1) (fs.map RealBlock.character)) (x : H),
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun y => realAdjacentMatrixWeight c.character.toMonoidHom Φ s y * B f (x * y))
        D.groupHaar ∧
      Integrable (fun y => realAdjacentMatrixWeight c.inverse.character.toMonoidHom
        (realRectangularSchwartzFourier a Φ) s y * B f (x * ι y)) D.groupHaar) ∧
    HasRealPairNormalizedGrowth [RealBlock.character c] (fs.map RealBlock.character)
      ([RealBlock.character c].map RealLocalJacquet.dualBlock)
      ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) a
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) 1
      (fun s => ∫ y, realAdjacentMatrixWeight c.character.toMonoidHom Φ s y * B f (x * y)
        ∂D.groupHaar)
      (fun s => ∫ y, realAdjacentMatrixWeight c.inverse.character.toMonoidHom
        (realRectangularSchwartzFourier a Φ) s y * B f (x * ι y) ∂D.groupHaar)

private theorem integral_sum_mul {μ : Measure H} (T : H → ℂ) (m : ℕ) (w : Fin m → ℂ)
    (C : Fin m → H → ℂ) (hC : ∀ j, Integrable (fun y => T y * C j y) μ) :
    (∫ y, T y * ∑ j, w j * C j y ∂μ) = ∑ j, w j * ∫ y, T y * C j y ∂μ := by
  have h (y : H) : T y * ∑ j, w j * C j y = ∑ j, w j * (T y * C j y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h]
  rw [integral_finsetSum Finset.univ (fun j _ => (hC j).const_mul _)]
  simp only [integral_const_mul]

set_option maxHeartbeats 1600000 in
theorem realGapSquareReflection : RealGapSquareReflectionStatement t := by
  classical
  intro D a c fs hfs Φ hΦfin B hB f x
  let es := fs.map RealBlock.character
  let μ := D.groupHaar
  have : μ.IsHaarMeasure := D.groupHaar_isHaar
  let ν : Measure O := Measure.haar
  let iK : O →* H := Unitary.toUnits
  have hiK : Continuous iK := Langlands.Archimedean.continuous_unitary_toUnits
  have hmem (k : O) : (iK k : H) ∈ unitaryCompact ℝ (t + 1) := k.property
  have hsurj (g : H) (hg : g ∈ unitaryCompact ℝ (t + 1)) : ∃ k : O, iK k = g :=
    ⟨⟨g.val, hg⟩, Units.ext rfl⟩
  have hdet (k : O) : |(iK k).val.det| = 1 :=
    Langlands.Archimedean.MaximalParabolicIntegration.abs_det_unitary ⟨iK k, hmem k⟩
  -- the reproducing compact weight
  obtain ⟨κ, hκ, hκfin, hrep⟩ := exists_realCompactMatrixWeight ν iK hiK c Φ Φ.continuous hΦfin
  have hrep' (A : M) : ∫ k, κ k * realCompactMatrixTranslate c.inverse Φ (iK k) A ∂ν = Φ A := by
    rw [← hrep A]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    change κ k * _ = κ k * _
    rw [realCompactMatrixTranslate_inverse_of_mem c Φ (hmem k)]
  have hΦint : Integrable (Φ : M → ℂ)
      (Langlands.RankinSelberg.rectangularMeasure (realSelfDualMeasure a) (t + 1) (t + 1)) := by
    let νR := realSelfDualMeasure a
    let : νR.measure.IsAddHaarMeasure := νR.isAddHaar
    let : (Langlands.RankinSelberg.rectangularMeasure νR (t + 1) (t + 1)).IsAddHaarMeasure :=
      Langlands.RankinSelberg.rectangularMeasure_isAddHaar νR (t + 1) (t + 1)
    exact Φ.integrable
  let Φd := realRectangularSchwartzFourier a Φ
  have hrepd (A : M) : ∫ k, κ k * realCompactMatrixTranslate c.inverse Φd (iK k) A ∂ν = Φd A := by
    have hF : (Φd : M → ℂ) = Langlands.HarmonicAnalysis.rectangularFourierIntegral
        (realScaledCharacter a) (realSelfDualMeasure a) Φ :=
      funext (realRectangularSchwartzFourier_apply a Φ)
    rw [hF]
    exact realLocalCompactFourierWeight a ν κ hκ c.inverse Φ hΦint hrep' A
  -- the compact projection and its finite expansion
  choose p hp hpB using fun g => realOrthogonalCompactProjectionPremise t es a κ hκ hκfin B hB f g
  obtain ⟨m, Wj, κ', hWj, hexp⟩ := realLocalCompactProjectionReduction (r := t) iK hiK hmem hsurj
    es a ν inferInstance κ hκ hκfin f B hB p (fun g y => hp g y) (fun y g => hpB g y)
  let C (j : Fin m) (z : H) : ℂ := ∫ k, κ' j k * (f : H → ℂ) (iK k * z) ∂ν
  have hSq (j : Fin m) := realAdjacentSquareGrowth (r := t) D iK hiK hmem ν (κ' j) (hWj j).2 a c
    Φ fs hfs f
  choose σsq hσsq using fun j => (hSq j).1
  obtain ⟨βsq, hβsq⟩ := (Set.finite_range σsq).bddAbove
  -- growth and continuity of the Whittaker value
  let V := B f
  have hV : V ∈ realUniformWhittakerModel t es a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hVc : Continuous V := (RealJacquet.splitModel_regular hV).2.1.continuous
  obtain ⟨CV, NV, hCV, hVb⟩ := splitModel_growth hV
  let Vd (g : H) : ℂ := V (x * ι g)
  have hVdc : Continuous Vd := hVc.comp (continuous_const.mul
    (Langlands.GeneralLinear.continuous_inverseTranspose (t + 1) ℝ))
  have hx1 : 1 ≤ realMatrixHeight x :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos t) x)
  have hVdb (g : H) : ‖Vd g‖ ≤ (CV * realMatrixHeight x ^ NV) * realMatrixHeight g ^ NV := by
    refine (hVb _).trans ?_
    rw [mul_assoc, ← mul_pow]
    apply mul_le_mul_of_nonneg_left _ hCV
    apply pow_le_pow_left₀ (RealPlaceRestriction.realMatrixHeight_nonneg _)
    rw [← realMatrixHeight_inverseTranspose g]
    exact realMatrixHeight_mul_le x (ι g)
  have hCVd : 0 ≤ CV * realMatrixHeight x ^ NV := mul_nonneg hCV (pow_nonneg (zero_le_one.trans hx1) _)
  -- a common half-plane
  let σ₀ : ℝ := (t : ℝ) + 1 + 2 * NV + |c.exponent.re| + |(c.inverse).exponent.re| + 1
  let σ : ℝ := max σ₀ βsq
  have hσ₀ (s : ℂ) (hs : σ < s.re) : σ₀ < s.re := (le_max_left _ _).trans_lt hs
  have hσj (s : ℂ) (hs : σ < s.re) (j : Fin m) : σsq j < s.re :=
    ((hβsq (Set.mem_range_self j)).trans (le_max_right _ _)).trans_lt hs
  have hwre (s : ℂ) (hs : σ < s.re) (d : RealCharacterData)
      (hd : |d.exponent.re| ≤ |c.exponent.re| + |(c.inverse).exponent.re|) :
      (t : ℝ) + 1 + 2 * NV ≤ d.exponent.re + (s + (t : ℂ) / 2).re := by
    have h := hσ₀ s hs
    have hd' := neg_abs_le d.exponent.re
    have ht : (0 : ℝ) ≤ (t : ℝ) / 2 := by positivity
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    simp only [σ₀] at h
    linarith
  have hcin : |c.exponent.re| ≤ |c.exponent.re| + |(c.inverse).exponent.re| :=
    le_add_of_nonneg_right (abs_nonneg _)
  have hcinv : |(c.inverse).exponent.re| ≤ |c.exponent.re| + |(c.inverse).exponent.re| :=
    le_add_of_nonneg_left (abs_nonneg _)
  -- the averaged ordinary and dual integrals
  have hOrd (s : ℂ) (hs : σ < s.re) :
      Integrable (fun y => realAdjacentMatrixWeight c.character.toMonoidHom Φ s y * V (x * y)) μ ∧
      (∫ y, realAdjacentMatrixWeight c.character.toMonoidHom Φ s y * V (x * y) ∂μ) =
        ∑ j, Wj j x * ∫ y, realAdjacentMatrixWeight c.character.toMonoidHom Φ s y * C j y ∂μ := by
    let w : ℂ := s + (t : ℂ) / 2
    let A := realWeightedMatrixTest c Φ w
    have hA : ∀ g, A g = ∫ k, κ k * A (iK k⁻¹ * g) ∂ν := fun g => by
      simpa only [map_inv] using realWeightedMatrixTest_reproduce iK hdet ν c Φ κ hrep w g
    have hInt := integrable_compactInsertion t μ ν iK hiK κ hκ c Φ hVc hCV hVb w
      (hwre s hs c hcin) x
    have hEq := ComplexJacquet.integral_of_compact_average iK hiK.measurable ν μ κ A
      (fun y => V (x * y)) hA hInt
    have hW (y : H) : realAdjacentMatrixWeight c.character.toMonoidHom Φ s y = A y :=
      matrixWeight_eq_weightedTest t c Φ s y
    simp_rw [hW]
    refine ⟨?_, ?_⟩
    · refine hInt.integral_prod_right.congr (ae_of_all _ fun y => ?_)
      change (∫ k, κ k * A (iK k⁻¹ * y) * V (x * y) ∂ν) = A y * V (x * y)
      rw [integral_mul_const, ← hA]
    · rw [hEq]
      have hE (y : H) : (∫ k, κ k * V (x * (iK k * y)) ∂ν) = ∑ j, Wj j x * C j y := by
        rw [← (hexp x y).1]
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        show κ k * B f (x * (iK k * y)) = κ k * B f (x * iK k * y)
        rw [mul_assoc x]
      simp_rw [hE]
      refine integral_sum_mul t A m (fun j => Wj j x) C (fun j => ?_)
      have h := (hσsq j s (hσj s hs j)).1
      simpa only [hW] using h
  have hDual (s : ℂ) (hs : σ < s.re) :
      Integrable (fun y => realAdjacentMatrixWeight c.inverse.character.toMonoidHom Φd s y *
        V (x * ι y)) μ ∧
      (∫ y, realAdjacentMatrixWeight c.inverse.character.toMonoidHom Φd s y * V (x * ι y) ∂μ) =
        ∑ j, Wj j x * ∫ y, realAdjacentMatrixWeight c.inverse.character.toMonoidHom Φd s y *
          C j (ι y) ∂μ := by
    let w : ℂ := s + (t : ℂ) / 2
    let A := realWeightedMatrixTest c.inverse Φd w
    have hA : ∀ g, A g = ∫ k, κ k * A (iK k⁻¹ * g) ∂ν := fun g => by
      simpa only [map_inv] using realWeightedMatrixTest_reproduce iK hdet ν c.inverse Φd κ hrepd w g
    have hInt := integrable_compactInsertion t μ ν iK hiK κ hκ c.inverse Φd hVdc hCVd hVdb w
      (hwre s hs c.inverse hcinv) 1
    have hEq := ComplexJacquet.integral_of_compact_average iK hiK.measurable ν μ κ A
      (fun y => Vd (1 * y)) hA hInt
    have hW (y : H) : realAdjacentMatrixWeight c.inverse.character.toMonoidHom Φd s y = A y :=
      matrixWeight_eq_weightedTest t c.inverse Φd s y
    have hVd1 (y : H) : Vd (1 * y) = V (x * ι y) := by rw [one_mul]
    simp_rw [hW]
    refine ⟨?_, ?_⟩
    · refine hInt.integral_prod_right.congr (ae_of_all _ fun y => ?_)
      change (∫ k, κ k * A (iK k⁻¹ * y) * Vd (1 * y) ∂ν) = A y * V (x * ι y)
      rw [integral_mul_const, ← hA, hVd1]
    · simp_rw [← hVd1]
      rw [hEq]
      have hE (y : H) : (∫ k, κ k * Vd (1 * (iK k * y)) ∂ν) = ∑ j, Wj j x * C j (ι y) := by
        rw [← (hexp x (ι y)).1]
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        show κ k * B f (x * ι (1 * (iK k * y))) = κ k * B f (x * iK k * ι y)
        rw [one_mul, map_mul, inverseTranspose_orthogonal (hmem k), mul_assoc x]
      simp_rw [hE]
      refine integral_sum_mul t A m (fun j => Wj j x) (fun j y => C j (ι y)) (fun j => ?_)
      have h := (hσsq j s (hσj s hs j)).2
      exact h.congr (ae_of_all _ fun y => congrArg (· * C j (ι y)) (hW y))
  have hG := HasRealPairNormalizedGrowth.sum Finset.univ
    (fun j s => Wj j x * ∫ z, realAdjacentMatrixWeight c.character.toMonoidHom Φ s z * C j z ∂μ)
    (fun j s => Wj j x * ∫ z, realAdjacentMatrixWeight c.inverse.character.toMonoidHom Φd s z *
      C j (ι z) ∂μ)
    (fun j _ => (hSq j).2.const_mul (Wj j x))
  refine ⟨⟨σ, fun s hs => ⟨(hOrd s hs).1, (hDual s hs).1⟩⟩, ?_⟩
  exact hG.congr (τ := σ) (fun s hs => ((hOrd s hs).2).symm) (fun s hs => ((hDual s hs).2).symm)

end Langlands.Global.RankinSelbergGlobal.RealGapSquareReflection
