import Langlands.Global.RankinSelberg.RealLocalEqualJointIntegrability
import Langlands.Global.RankinSelberg.ComplexLocalCompactAveraging
import Langlands.Global.RankinSelberg.ComplexLocalCompactWeight
import Langlands.Global.RankinSelberg.RealMatrixConvergence
import Langlands.Global.RankinSelberg.RealUnequalConvergence
import Langlands.Global.RankinSelberg.RealUnequalPairConvergence
import Langlands.Global.RankinSelberg.RealWhittakerGauge
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Global.RankinSelberg.RealPrincipalSeriesOrbitWord

/-! # The real equal-rank finite products in the dominant chamber -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean Langlands.Whittaker
open Langlands.RankinSelberg (LeftUnipotentQuotient unipotent_det)
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Matrix.Norms.Operator SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData charData_character_apply)
open RealLocalWhittaker (regularFunctions iteratedRightDerivative)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

private local instance (j : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear (j + 1) ℝ) := by
  let _ : LocallyCompactSpace (Matrix (Fin (j + 1)) (Fin (j + 1)) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (j + 1) → Fin (j + 1) → ℝ))
  exact Units.isOpenEmbedding_val.locallyCompactSpace

private local instance (j : ℕ) : SecondCountableTopology (Langlands.GeneralLinear (j + 1) ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

private local instance (j : ℕ) : SigmaCompactSpace (LeftUnipotentQuotient j ℝ) := by
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective
    (s := QuotientGroup.rightRel (GeneralLinear.upperUnipotent (j + 1) ℝ)))]
  exact isSigmaCompact_range continuous_quotient_mk'

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "U" => GeneralLinear.upperUnipotent (t + 2) ℝ
local notation "Q" => LeftUnipotentQuotient t ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "pad" => (padGL (R := ℝ) (Nat.le_succ (t + 1)))
local notation "P" => (ArchimedeanLocal.detPower (K := ℝ) realNormalizedAbs)
local notation "gap" => Nat.lt_succ_self t

/-! ### Weighted square tests and their compact translates -/

/-- A square test multiplied by the real determinant character `d` with the absolute
determinant power `w`. -/
def realWeightedMatrixTest {j : ℕ} (d : RealCharacterData) (Ψ : Matrix (Fin j) (Fin j) ℝ → ℂ)
    (w : ℂ) (g : Langlands.GeneralLinear j ℝ) : ℂ :=
  Ψ g.val * determinantWeight d w g

/-- The left translate of a square test by an invertible matrix `g`, multiplied by the
character `d` of `det g⁻¹`. -/
def realCompactMatrixTranslate {j : ℕ} (d : RealCharacterData)
    (Ψ : Matrix (Fin j) (Fin j) ℝ → ℂ) (g : Langlands.GeneralLinear j ℝ)
    (A : Matrix (Fin j) (Fin j) ℝ) : ℂ :=
  (d.character (determinant g⁻¹) : ℂ) * Ψ ((g⁻¹).val * A)

private theorem determinantWeight_apply {j : ℕ} (c : RealCharacterData) (w : ℂ)
    (g : Langlands.GeneralLinear j ℝ) :
    determinantWeight c w g = (c.character (determinant g) : ℂ) * ((|g.val.det| : ℝ) : ℂ) ^ w :=
  rfl

/-- At a character of prescribed parity, the exponent of the character moves into the
absolute determinant power. -/
theorem determinantWeight_charData_shift {j : ℕ} (e : Fin 2) (z w : ℂ)
    (g : Langlands.GeneralLinear j ℝ) :
    determinantWeight (charData e z) w g = determinantWeight (charData e 0) (z + w) g := by
  have h : ((|g.val.det| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (determinant g).ne_zero)
  rw [determinantWeight_apply, determinantWeight_apply, charData_character_apply,
    charData_character_apply]
  unfold Langlands.Archimedean.RealJacquetFrobenius.charFun
  change ((((g.val.det / |g.val.det| : ℝ)) : ℂ) ^ e.val * ((|g.val.det| : ℝ) : ℂ) ^ z) *
      ((|g.val.det| : ℝ) : ℂ) ^ w =
    ((((g.val.det / |g.val.det| : ℝ)) : ℂ) ^ e.val * ((|g.val.det| : ℝ) : ℂ) ^ (0 : ℂ)) *
      ((|g.val.det| : ℝ) : ℂ) ^ (z + w)
  rw [Complex.cpow_zero, mul_one, mul_assoc, ← Complex.cpow_add _ _ h]

theorem continuous_determinantWeight {j : ℕ} (c : RealCharacterData) (z : ℂ) :
    Continuous (determinantWeight c z : Langlands.GeneralLinear j ℝ → ℂ) := by
  have hval : Continuous (fun g : Langlands.GeneralLinear j ℝ => g.val.det) :=
    Units.continuous_val.matrix_det
  have hbase : Continuous (fun g : Langlands.GeneralLinear j ℝ => ((|g.val.det| : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hval.abs
  have hpow : Continuous (fun g : Langlands.GeneralLinear j ℝ => ((|g.val.det| : ℝ) : ℂ) ^ z) := by
    refine continuous_iff_continuousAt.mpr fun g => ?_
    have h : ContinuousAt (fun x : ℂ => x ^ z) ((|g.val.det| : ℝ) : ℂ) :=
      continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr
        (abs_pos.mpr (determinant g).ne_zero))
    exact ContinuousAt.comp (f := fun k : Langlands.GeneralLinear j ℝ => ((|k.val.det| : ℝ) : ℂ))
      h (hbase.continuousAt (x := g))
  exact (Units.continuous_val.comp (c.character.continuous.comp
    GeneralLinear.determinantContinuous.continuous)).mul hpow

/-- A weight reproducing the square test under compact translation reproduces the
weighted test, for every compact element of absolute determinant one. -/
theorem realWeightedMatrixTest_reproduce {K : Type*} [MeasurableSpace K] {j : ℕ}
    (ι : K → Langlands.GeneralLinear j ℝ) (hι : ∀ k, |(ι k).val.det| = 1) (ν : Measure K)
    (d : RealCharacterData) (Ψ : Matrix (Fin j) (Fin j) ℝ → ℂ) (κ : K → ℂ)
    (hΨ : ∀ A, ∫ k, κ k * realCompactMatrixTranslate d Ψ (ι k) A ∂ν = Ψ A)
    (w : ℂ) (g : Langlands.GeneralLinear j ℝ) :
    realWeightedMatrixTest d Ψ w g =
      ∫ k, κ k * realWeightedMatrixTest d Ψ w ((ι k)⁻¹ * g) ∂ν := by
  have hk (k : K) : determinantWeight d w (ι k)⁻¹ = (d.character (determinant (ι k)⁻¹) : ℂ) := by
    have h1 : |((ι k)⁻¹).val.det| = 1 := by
      change |((determinant (ι k)⁻¹ : ℝˣ) : ℝ)| = 1
      rw [map_inv, Units.val_inv_eq_inv_val, abs_inv, inv_eq_one]
      exact hι k
    rw [determinantWeight_apply, h1, Complex.ofReal_one, Complex.one_cpow, mul_one]
  change Ψ g.val * determinantWeight d w g = _
  rw [← hΨ g.val, ← integral_mul_const]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun k => ?_
  simp only [realWeightedMatrixTest, realCompactMatrixTranslate, map_mul, hk, Units.val_mul]
  ring

/-- A continuous square test whose compact left translates span a finite-dimensional space
admits a continuous reproducing compact weight with finite-dimensional left-translate span. -/
theorem exists_realCompactMatrixWeight {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K] {j : ℕ} (μ : Measure K) [μ.IsHaarMeasure]
    (ι : K →* Langlands.GeneralLinear j ℝ) (hι : Continuous ι) (d : RealCharacterData)
    (Ψ : Matrix (Fin j) (Fin j) ℝ → ℂ) (hΨ : Continuous Ψ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : K => fun A : Matrix (Fin j) (Fin j) ℝ => Ψ (((ι k)⁻¹).val * A)))) :
    ∃ κ : K → ℂ, Continuous κ ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : K => fun k => κ (h⁻¹ * k))) ∧
      ∀ A, ∫ k, κ k * realCompactMatrixTranslate d Ψ (ι k) A ∂μ = Ψ A := by
  let F : K → Matrix (Fin j) (Fin j) ℝ → ℂ := fun k => realCompactMatrixTranslate d Ψ (ι k)
  have hinv : Continuous fun k => (ι k)⁻¹ := hι.inv
  have hcont (A : Matrix (Fin j) (Fin j) ℝ) : Continuous fun k => F k A :=
    (Units.continuous_val.comp (d.character.continuous.comp
      (GeneralLinear.determinantContinuous.continuous.comp hinv))).mul
      (hΨ.comp ((Units.continuous_val.comp hinv).mul continuous_const))
  have hF : FiniteDimensional ℂ (Submodule.span ℂ (Set.range F)) := by
    let T := Submodule.span ℂ
      (Set.range fun k : K => fun A : Matrix (Fin j) (Fin j) ℝ => Ψ (((ι k)⁻¹).val * A))
    let : FiniteDimensional ℂ T := hfin
    apply Submodule.finiteDimensional_of_le (S₂ := T)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact T.smul_mem (d.character (determinant (ι k)⁻¹) : ℂ) (Submodule.subset_span ⟨k, rfl⟩)
  have hshift (h : K) (A : Matrix (Fin j) (Fin j) ℝ) :
      ∃ (c : ℂ) (B : Matrix (Fin j) (Fin j) ℝ), ∀ k, F (h⁻¹ * k) A = c * F k B := by
    refine ⟨(d.character (determinant (ι h)) : ℂ), (ι h).val * A, fun k => ?_⟩
    simp only [F, realCompactMatrixTranslate, map_mul, map_inv, mul_inv_rev, inv_inv,
      Units.val_mul, Matrix.mul_assoc]
    ring
  obtain ⟨κ, hκc, hκfin, hκ⟩ := ComplexJacquet.exists_compactWeight_of_finite_orbit μ F hcont hF hshift
  refine ⟨κ, hκc, hκfin, fun A => (hκ A).trans ?_⟩
  simp only [F, realCompactMatrixTranslate, map_one, inv_one, Units.val_one,
    one_mul]

/-! ### Compact insertion -/

/-- For a coefficient of polynomial height growth, the compact averaging kernel against a
weighted square test is integrable at every fixed left multiplier once the total
determinant exponent is large. -/
theorem integrable_realCompactInsertion {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure H) [μ.IsHaarMeasure] (ν : Measure K) [IsFiniteMeasure ν]
    (ι : K →* H) (hι : Continuous ι) (κ : K → ℂ) (hκ : Continuous κ)
    (d : RealCharacterData) (Ψ : 𝓢(Y, ℂ)) {V : H → ℂ} (hVc : Continuous V)
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hV : ∀ g, ‖V g‖ ≤ C * realMatrixHeight g ^ N)
    (w : ℂ) (hw : (t : ℝ) + 2 + 2 * N ≤ d.exponent.re + w.re) (x : H) :
    Integrable (fun p : K × H =>
      κ p.1 * realWeightedMatrixTest d Ψ w (ι p.1⁻¹ * p.2) * V (x * p.2)) (ν.prod μ) := by
  let A := realWeightedMatrixTest d Ψ w
  let E (g : H) : ℝ := realMatrixHeight g
  have hE : Continuous E := continuous_realMatrixHeight
  have hE0 (g : H) : 0 ≤ E g := RealPlaceRestriction.realMatrixHeight_nonneg g
  have hA : Continuous A :=
    (Ψ.continuous.comp Units.continuous_val).mul (continuous_determinantWeight d w)
  refine (ComplexJacquet.integrable_compact_average_iff ι hι.measurable ν μ κ A
    (fun g => V (x * g))).mpr ?_
  let T (k : K) := C * E (x * ι k) ^ N * ‖κ k‖
  have hT : Continuous T :=
    (((hE.comp (continuous_const.mul hι)).pow N).const_mul C).mul hκ.norm
  have hTi : Integrable T ν :=
    hT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace T)
  let B (g : H) := E g ^ N * ‖A g‖
  have hB : Integrable B μ := by
    have h := Langlands.GodementJacquet.integrable_realMatrixWeightedNorm (r := t + 1) μ
      (f := fun g : H => ((E g ^ N : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp (hE.pow N)).measurable Ψ (C := 1) zero_le_one
      (fun g => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hE0 g) N), one_mul])
      (q := d.exponent.re + w.re) (by push_cast; linarith)
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
  have hH : E (x * (ι k * g)) ≤ E (x * ι k) * E g := by
    rw [← mul_assoc]
    exact realMatrixHeight_mul_le _ _
  have hP : ‖V (x * (ι k * g))‖ ≤ C * (E (x * ι k) ^ N * E g ^ N) := by
    rw [← mul_pow]
    exact (hV _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hE0 _) hH N) hC)
  simp only [norm_mul]
  calc
    ‖A g‖ * (‖κ k‖ * ‖V (x * (ι k * g))‖) ≤
        ‖A g‖ * (‖κ k‖ * (C * (E (x * ι k) ^ N * E g ^ N))) := by gcongr
    _ = T k * B g := by simp only [T, B]; ring

/-! ### Quotient representatives -/

/-- Under opposite Whittaker laws, the corank-one integrand may be evaluated at the
continuous section of the quotient instead of the chosen representative. -/
theorem realUnequalIntegrand_representative {a : ℝˣ} {V : H → ℂ} {W : G → ℂ}
    (hV : V ∈ regularFunctions (t + 1) (-a)) (hW : W ∈ regularFunctions t a) (s : ℂ) (q : Q) :
    realUnequalIntegrand gap V W s q =
      V (pad (quotientRepresentative t q)) *
        (W (quotientRepresentative t q) * P (quotientRepresentative t q) (s - 1 / 2)) := by
  let v := RealIwasawa.npart q.out
  have hv : v.val * quotientRepresentative t q = q.out := by
    have h := (unipotentQuotientHomeomorph t).right_inv q.out
    change v.val * quotientRepresentative t (Quotient.mk _ q.out) = q.out at h
    rwa [Quotient.out_eq] at h
  have hshift : (t + 1 - t : ℕ) = 1 := by omega
  simp only [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, hshift, Nat.cast_one]
  rw [← hv]
  let h := quotientRepresentative t q
  have hpad : padGL (Nat.le_of_lt (Nat.succ_lt_succ gap)) v.val ∈
      GeneralLinear.upperUnipotent (t + 2) ℝ :=
    RealUnequalConvergence.padGL_mem_upperUnipotent _ v.2
  have hdet : P (v.val * h) (s - 1 / 2) = P h (s - 1 / 2) := by
    simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]
  rw [map_mul, hV.1 _ hpad, hW.1 v.val v.2, hdet,
    RealUnequalConvergence.realWhittakerCharacter_padGL gap]
  have hc := RealEqualConvergence.realWhittakerCharacter_mul_neg a v.val
  calc
    _ = (realWhittakerCharacter a v.val * realWhittakerCharacter (-a) v.val) *
        (V (padGL (Nat.le_of_lt (Nat.succ_lt_succ gap)) h) * (W h * P h (s - 1 / 2))) := by ring
    _ = _ := by rw [hc, one_mul]

/-! ### The finite products -/

variable (t) in
/-- In the dominant chamber of the separated exponent, a compact expansion of the larger
coefficient and a reproducing compact weight for the square test separate Jacquet's
unfolded integral (8.1) into finitely many corank-one integrals times matrix integrals.
Only the spectral variable of the matrix integrals receives the separated exponent. -/
def RealLocalEqualShiftedProductsStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1))
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ι : K →* H), Continuous ι → (∀ k, |(ι k).val.det| = 1) →
  ∀ (κ : K → ℂ), Continuous κ →
  ∀ (a : ℝˣ) (e : Fin 2) (ds es : List RealBlock) (W : G → ℂ) (V : H → ℂ),
    W ∈ realUniformWhittakerModel t ds a → V ∈ realUniformWhittakerModel (t + 1) es (-a) →
  ∀ (Ψ : 𝓢(Y, ℂ)),
    (∀ A, ∫ k, κ k * realCompactMatrixTranslate (charData e 0) Ψ (ι k) A ∂ν = Ψ A) →
  ∀ (c : ℕ) (Vj bj : Fin c → H → ℂ) (Z : Fin c → ℂ → ℂ),
    (∀ j, Vj j ∈ realUniformWhittakerModel (t + 1) es (-a)) →
    (∀ x g, (∫ k, κ k * V (x * ι k * g) ∂ν) = ∑ j, Vj j x * bj j g) →
    (∃ β : ℝ, ∀ w : ℂ, β < w.re → ∀ j,
      Integrable (fun g => realWeightedMatrixTest (charData e 0) Ψ (w + (m : ℂ) / 2) g * bj j g)
        D'.groupHaar ∧
      Z j w = ∫ g, realWeightedMatrixTest (charData e 0) Ψ (w + (m : ℂ) / 2) g * bj j g
        ∂D'.groupHaar) →
    ∃ τ σ : ℝ, ∀ z s : ℂ, τ < z.re → σ < s.re →
      ∫ p, equalUnfoldedKernel (charData e z) Ψ W V s p ∂(D.measure.prod D'.groupHaar) =
        ∑ j, realUnequalIntegral gap D (Vj j) W s * Z j (s + z)

variable (t) in
/-- If joint integrability is available above a prescribed leading abscissa, the same
abscissa and positivity of the leading real part suffice for the shifted product identity
on a right spectral half-plane. -/
def RealLocalEqualShiftedProductsWithIntegrabilityStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1))
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ι : K →* H), Continuous ι → (∀ k, |(ι k).val.det| = 1) →
  ∀ (κ : K → ℂ), Continuous κ →
  ∀ (a : ℝˣ) (e : Fin 2) (ds es : List RealBlock) (W : G → ℂ) (V : H → ℂ),
    W ∈ realUniformWhittakerModel t ds a → V ∈ realUniformWhittakerModel (t + 1) es (-a) →
  ∀ (Ψ : 𝓢(Y, ℂ)),
    (∀ A, ∫ k, κ k * realCompactMatrixTranslate (charData e 0) Ψ (ι k) A ∂ν = Ψ A) →
  ∀ (c : ℕ) (Vj bj : Fin c → H → ℂ) (Z : Fin c → ℂ → ℂ),
    (∀ j, Vj j ∈ realUniformWhittakerModel (t + 1) es (-a)) →
    (∀ x g, (∫ k, κ k * V (x * ι k * g) ∂ν) = ∑ j, Vj j x * bj j g) →
    (∃ β : ℝ, ∀ w : ℂ, β < w.re → ∀ j,
      Integrable (fun g => realWeightedMatrixTest (charData e 0) Ψ (w + (m : ℂ) / 2) g * bj j g)
        D'.groupHaar ∧
      Z j w = ∫ g, realWeightedMatrixTest (charData e 0) Ψ (w + (m : ℂ) / 2) g * bj j g
        ∂D'.groupHaar) →
    ∀ τ σ : ℝ,
      (∀ z s : ℂ, τ < z.re → σ < s.re →
        Integrable (equalUnfoldedKernel (charData e z) Ψ W V s) (D.measure.prod D'.groupHaar)) →
    ∃ σ' : ℝ, ∀ z s : ℂ, τ < z.re → 0 < z.re → σ' < s.re →
      ∫ p, equalUnfoldedKernel (charData e z) Ψ W V s p ∂(D.measure.prod D'.groupHaar) =
        ∑ j, realUnequalIntegral gap D (Vj j) W s * Z j (s + z)

set_option maxHeartbeats 1600000 in
theorem realLocalEqualShiftedProducts_of_integrable :
    RealLocalEqualShiftedProductsWithIntegrabilityStatement t := by
  intro D D' K _ _ _ _ _ _ ν _ ι hι hdet κ hκ a e ds es W V hW hV Ψ hΨ c Vj bj Z hVj hExp hZ τ σ hJ
  let := D.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let := D'.groupHaar_isHaar
  obtain ⟨hWreg, hWgrowth⟩ := realUniformWhittakerRegularity t ds a W hW
  obtain ⟨hVreg, -⟩ := realUniformWhittakerRegularity (t + 1) es (-a) V hV
  have hWr : W ∈ regularFunctions t a := hWreg []
  have hVr : V ∈ regularFunctions (t + 1) (-a) := hVreg []
  have hVc : Continuous V := hVr.2.1.continuous
  obtain ⟨CV, NV, hCV, hVb⟩ := hVr.2.2
  have hVjr (j : Fin c) : Vj j ∈ regularFunctions (t + 1) (-a) :=
    (realUniformWhittakerRegularity (t + 1) es (-a) (Vj j) (hVj j)).1 []
  have hQ (j : Fin c) : ∃ σj : ℝ, ∀ s : ℂ, σj < s.re →
      Integrable (realUnequalIntegrand gap (Vj j) W s) D.measure := by
    obtain ⟨hreg, hgr⟩ := realUniformWhittakerRegularity (t + 1) es (-a) (Vj j) (hVj j)
    obtain ⟨σj, h, -⟩ := RealUnequalConvergence.exists_convergence_of_regular gap D hreg hgr
      (by simpa only [neg_neg] using hWreg) hWgrowth
    exact ⟨σj, h⟩
  choose σj hσj using hQ
  obtain ⟨βQ, hβQ⟩ := (Set.finite_range σj).bddAbove
  obtain ⟨β, hβ⟩ := hZ
  let σ₀ : ℝ := (t : ℝ) + 2 + 2 * NV - ((t : ℝ) + 1) / 2
  refine ⟨max σ (max σ₀ (max β βQ)), ?_⟩
  intro z s hzτ hz0 hs
  simp only [max_lt_iff] at hs
  obtain ⟨hsσ, hsσ₀, hsβ, hsQ⟩ := hs
  have hm : ((m : ℂ) / 2).re = ((t : ℝ) + 1) / 2 := by
    rw [show ((m : ℂ) / 2) = ((((t : ℝ) + 1) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hsz : β < (s + z).re := by rw [Complex.add_re]; linarith
  let d₀ := charData e 0
  let A := realWeightedMatrixTest d₀ Ψ (s + z + (m : ℂ) / 2)
  let F : Q → H → ℂ := fun q g => V (pad (quotientRepresentative t q) * g) *
    (W (quotientRepresentative t q) * P (quotientRepresentative t q) (s - 1 / 2))
  have hker (x : Q × H) : equalUnfoldedKernel (charData e z) Ψ W V s x = A x.2 * F x.1 x.2 := by
    simp only [equalUnfoldedKernel, A, F, realWeightedMatrixTest, d₀]
    rw [determinantWeight_charData_shift, show z + (s + (m : ℂ) / 2) = s + z + (m : ℂ) / 2 by ring]
    ring
  have hProd : Integrable (fun x : Q × H => A x.2 * F x.1 x.2) (D.measure.prod D'.groupHaar) :=
    (hJ z s hzτ hsσ).congr (ae_of_all _ hker)
  have hw : (t : ℝ) + 2 + 2 * NV ≤ d₀.exponent.re + (s + z + (m : ℂ) / 2).re := by
    have h0 : d₀.exponent.re = 0 := Complex.zero_re
    rw [h0, Complex.add_re, Complex.add_re, hm]
    dsimp only [σ₀] at hsσ₀
    linarith
  have hInt : ∀ᵐ q ∂D.measure, Integrable
      (fun x : K × H => κ x.1 * A (ι x.1⁻¹ * x.2) * F q x.2) (ν.prod D'.groupHaar) := by
    refine ae_of_all _ fun q => ?_
    have h := (integrable_realCompactInsertion D'.groupHaar ν ι hι κ hκ d₀ Ψ hVc hCV hVb
      (s + z + (m : ℂ) / 2) hw (pad (quotientRepresentative t q))).mul_const
      (W (quotientRepresentative t q) * P (quotientRepresentative t q) (s - 1 / 2))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [F, A]
    ring
  have hA : ∀ g, A g = ∫ k, κ k * A (ι k⁻¹ * g) ∂ν := by
    intro g
    simp only [map_inv]
    exact realWeightedMatrixTest_reproduce ι hdet ν d₀ Ψ κ hΨ _ g
  have hExp' : ∀ q g, (∫ k, κ k * F q (ι k * g) ∂ν) =
      ∑ j, realUnequalIntegrand gap (Vj j) W s q * bj j g := by
    intro q g
    calc
      (∫ k, κ k * F q (ι k * g) ∂ν) =
          ∫ k, (κ k * V (pad (quotientRepresentative t q) * ι k * g)) *
            (W (quotientRepresentative t q) * P (quotientRepresentative t q) (s - 1 / 2)) ∂ν :=
        integral_congr_ae (ae_of_all _ fun k => by simp only [F, mul_assoc])
      _ = (∫ k, κ k * V (pad (quotientRepresentative t q) * ι k * g) ∂ν) *
            (W (quotientRepresentative t q) * P (quotientRepresentative t q) (s - 1 / 2)) :=
        integral_mul_const _ _
      _ = _ := by
        rw [hExp, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [realUnequalIntegrand_representative (hVjr j) hWr s q]
        ring
  have ha (j : Fin c) : Integrable (realUnequalIntegrand gap (Vj j) W s) D.measure :=
    hσj j s ((hβQ (Set.mem_range_self j)).trans_lt hsQ)
  have hb (j : Fin c) : Integrable (fun g => A g * bj j g) D'.groupHaar := (hβ (s + z) hsz j).1
  calc
    ∫ x, equalUnfoldedKernel (charData e z) Ψ W V s x ∂(D.measure.prod D'.groupHaar) =
        ∫ x, A x.2 * F x.1 x.2 ∂(D.measure.prod D'.groupHaar) :=
      integral_congr_ae (ae_of_all _ hker)
    _ = ∫ g, A g * (∫ q, F q g ∂D.measure) ∂D'.groupHaar := by
      rw [integral_prod_symm _ hProd]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      dsimp only
      exact integral_const_mul _ _
    _ = ∑ j, (∫ q, realUnequalIntegrand gap (Vj j) W s q ∂D.measure) *
          (∫ g, A g * bj j g ∂D'.groupHaar) :=
      ComplexJacquet.integral_prod_eq_sum_mul_of_compact_average ι hι.measurable ν D'.groupHaar
        D.measure κ A F hA hProd hInt (fun j => realUnequalIntegrand gap (Vj j) W s) bj hExp' ha hb
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hβ (s + z) hsz j).2]
      rfl

set_option maxHeartbeats 1600000 in
theorem realLocalEqualShiftedProducts : RealLocalEqualShiftedProductsStatement t := by
  intro D D' K _ _ _ _ _ _ ν _ ι hι hdet κ hκ a e ds es W V hW hV Ψ hΨ c Vj bj Z hVj hExp hZ
  obtain ⟨hWreg, hWgrowth⟩ := realUniformWhittakerRegularity t ds a W hW
  obtain ⟨hVreg, hVgrowth⟩ := realUniformWhittakerRegularity (t + 1) es (-a) V hV
  have hWr : W ∈ regularFunctions t a := hWreg []
  have hVr : V ∈ regularFunctions (t + 1) (-a) := hVreg []
  have hWc : Continuous W := hWr.2.1.continuous
  have hVc : Continuous V := hVr.2.1.continuous
  have hWg : RealEqualConvergence.HasGauge W := RealWhittakerGauge.exists_gauge_bound hWreg hWgrowth
  have hVg : RealEqualConvergence.HasGauge V := RealWhittakerGauge.exists_gauge_bound hVreg hVgrowth
  have hVu : ∀ (u : U) (g : H), ‖V (u.val * g)‖ = ‖V g‖ := by
    intro u g
    rw [hVr.1 u.val u.2 g, norm_mul, RealUnequalPairConvergence.norm_realWhittakerCharacter,
      one_mul]
  obtain ⟨ρ, σ, hJ⟩ := realLocalEqualJointIntegrability D D' W V hWc hVc hWg hVg hVu
  have hJ' (z s : ℂ) (hz : ρ < z.re) (hs : σ < s.re) :
      Integrable (equalUnfoldedKernel (charData e z) Ψ W V s) (D.measure.prod D'.groupHaar) := by
    obtain ⟨_, _, _, h⟩ := hJ z.re s.re hz.le hs
    exact (h Ψ (charData e z) s rfl rfl).1
  obtain ⟨σ', h⟩ := realLocalEqualShiftedProducts_of_integrable D D' K ν ι hι hdet κ hκ a e ds es W V
    hW hV Ψ hΨ c Vj bj Z hVj hExp hZ ρ σ hJ'
  exact ⟨max ρ 0, σ', fun z s hz => h z s ((le_max_left _ _).trans_lt hz) ((le_max_right _ _).trans_lt hz)⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
