import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.ComplexLocalUnipotentBlockMeasure
import Langlands.Analysis.Local.QuotientNormalizingFunction
import Langlands.Representation.Archimedean.ComplexGeneralLinearHaarDensity
import Langlands.Representation.Archimedean.ComplexPartialJacquet
import Langlands.Global.RankinSelberg.UnequalAnalyticMatrices
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints

/-! # The last-row fiber of the complex unipotent quotient -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLastRowFiber

open Langlands.GeneralLinear Langlands.QuotientIntegration ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity
  (complexGeneralLinearHaar matrixLebesgue normSqHom continuous_normSqHom)
open Langlands.RankinSelberg.GLDeterminantDensity (matrixWeight)
open Langlands.HarmonicAnalysis (rectangularJoin rectangularJoin_last rectangularJoin_castSucc)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable
  archimedeanComplexQBorel

section Transfer

variable (n : ℕ)

local notation "Mat" => Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
local notation "GL" => Langlands.GeneralLinear (n + 1) ℂ

/-- A function on the group, extended by zero to all matrices and weighted by the
inverse determinant density. -/
def matrixDensity (f : GL → ℂ) (X : Mat) : ℂ :=
  (matrixWeight (n + 1) normSqHom X : ℝ) • Function.extend Units.val f 0 X

theorem matrixDensity_val (f : GL → ℂ) (g : GL) :
    matrixDensity n f g.val = (matrixWeight (n + 1) normSqHom g.val : ℝ) • f g := by
  rw [matrixDensity, Units.val_injective.extend_apply]

theorem matrixDensity_of_not_mem (f : GL → ℂ) {X : Mat}
    (hX : X ∉ Set.range (Units.val : GL → Mat)) : matrixDensity n f X = 0 := by
  rw [matrixDensity, Function.extend_apply' _ _ _ (by simpa using hX), Pi.zero_apply, smul_zero]

theorem integral_complexGeneralLinearHaar (f : GL → ℂ) :
    ∫ g, f g ∂complexGeneralLinearHaar (n + 1) = ∫ X, matrixDensity n f X ∂matrixLebesgue (n + 1) := by
  have h := Langlands.RankinSelberg.GLDeterminantDensity.integral_weightedRestriction (r := n + 1)
    normSqHom continuous_normSqHom (matrixLebesgue (n + 1)) (Function.extend Units.val f 0)
  simp only [Units.val_injective.extend_apply] at h
  refine h.trans ?_
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rfl
  · intro X hX
    exact matrixDensity_of_not_mem n f hX

theorem integrable_complexGeneralLinearHaar_iff (f : GL → ℂ) :
    Integrable f (complexGeneralLinearHaar (n + 1)) ↔
      Integrable (matrixDensity n f) (matrixLebesgue (n + 1)) := by
  have h := Langlands.Archimedean.ComplexGeneralLinearHaarDensity.integrable_complexGeneralLinearHaar_iff
    (n := n + 1) (Function.extend Units.val f 0)
  simp only [Units.val_injective.extend_apply] at h
  rw [h]
  refine integrableOn_iff_integrable_of_support_subset ?_
  intro X hX
  by_contra hX'
  exact hX (matrixDensity_of_not_mem n f hX')

theorem measurable_matrixDensity {f : GL → ℂ} (hf : Measurable f) :
    Measurable (matrixDensity n f) := by
  have he := (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (n + 1)).measurableEmbedding
  exact (NNReal.continuous_coe.measurable.comp
    (Langlands.RankinSelberg.GLDeterminantDensity.measurable_matrixWeight (n + 1) normSqHom
      continuous_normSqHom)).smul (he.measurable_extend hf measurable_const)

theorem lintegral_complexGeneralLinearHaar (f : GL → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂complexGeneralLinearHaar (n + 1) =
      ∫⁻ X, (matrixWeight (n + 1) normSqHom X : ℝ≥0∞) * Function.extend Units.val f 0 X
        ∂matrixLebesgue (n + 1) := by
  have he := (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (n + 1)).measurableEmbedding
  have hext : Measurable (Function.extend (Units.val : GL → Mat) f 0) :=
    he.measurable_extend hf measurable_const
  have h1 : ∫⁻ g, f g ∂complexGeneralLinearHaar (n + 1) =
      ∫⁻ X, Function.extend Units.val f 0 X ∂(complexGeneralLinearHaar (n + 1)).map Units.val := by
    rw [he.lintegral_map]
    simp only [Units.val_injective.extend_apply]
  rw [h1]
  change ∫⁻ X, _ ∂(Langlands.RankinSelberg.GLDeterminantDensity.weightedRestriction (n + 1)
    normSqHom (matrixLebesgue (n + 1))).map Units.val = _
  rw [Langlands.RankinSelberg.GLDeterminantDensity.weightedRestriction_map_ambient,
    lintegral_withDensity_eq_lintegral_mul _ _ hext]
  · refine lintegral_congr fun X => ?_
    by_cases hX : X ∈ Set.range (Units.val : GL → Mat)
    · simp only [Pi.mul_apply, Set.indicator_of_mem hX]
    · simp only [Pi.mul_apply, Set.indicator_of_notMem hX,
        Function.extend_apply' _ _ _ (by simpa using hX), Pi.zero_apply, mul_zero]
  · exact (measurable_coe_nnreal_ennreal.comp
      (Langlands.RankinSelberg.GLDeterminantDensity.measurable_matrixWeight (n + 1) normSqHom
        continuous_normSqHom)).indicator
      (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (n + 1)).isOpen_range.measurableSet

end Transfer

local instance complexGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n ℂ) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact inferInstance

local instance complexGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).isEmbedding.secondCountableTopology

local instance complexNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent n ℂ) :=
  Langlands.GeneralLinear.UpperUnipotent.locallyCompactSpace

section Fiber

variable (k : ℕ)

local notation "G" => Langlands.GeneralLinear (k + 1 + 1) ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (k + 1 + 1) ℂ
local notation "Mat" => Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ
local notation "Row" => Fin (k + 1 + 1) → ℂ
local notation "Rows" => Fin (k + 1) → Fin (k + 1 + 1) → ℂ

/-- The rows of a matrix with given last row and given first rows. -/
def joinRows (η : Row) (A : Rows) : Mat :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => Row) (Fin.last (k + 1))).symm (η, A)

@[simp] theorem joinRows_last (η : Row) (A : Rows) : joinRows k η A (Fin.last (k + 1)) = η := by
  simp [joinRows]

@[simp] theorem joinRows_castSucc (η : Row) (A : Rows) (i : Fin (k + 1)) :
    joinRows k η A i.castSucc = A i := by
  simp [joinRows]

/-- The weighted group function `g ↦ ρ(g) F(g)`. -/
def weighted (F : G → ℂ) (ρ : G → ℝ≥0) (g : G) : ℂ := (ρ g : ℂ) * F g

/-- Integral of the weighted density over the first rows, as a function of the last row. -/
def fiber (F : G → ℂ) (ρ : G → ℝ≥0) (η : Row) : ℂ :=
  ∫ A : Rows, matrixDensity (k + 1) (weighted k F ρ) (joinRows k η A)

private theorem matrixLebesgue_eq :
    matrixLebesgue (k + 1 + 1) = (volume : Measure (Fin (k + 1 + 1) → Fin (k + 1 + 1) → ℂ)) :=
  rfl

private theorem measurePreserving_joinRows :
    MeasurePreserving (fun p : Row × Rows => joinRows k p.1 p.2)
      ((volume : Measure Row).prod (volume : Measure Rows))
      (matrixLebesgue (k + 1 + 1)) := by
  rw [matrixLebesgue_eq]
  exact (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1 + 1) => (volume : Measure Row))
    (Fin.last (k + 1))).symm

/-- The last row of a group element. -/
def lastRow (g : G) : Row := g.val (Fin.last (k + 1))

theorem lastRow_unipotent_mul (u : N) (g : G) : lastRow k (u.val * g) = lastRow k g := by
  funext j
  simp only [lastRow, Units.val_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last (k + 1))]
  · rw [UpperUnipotent.entry_diag, one_mul]
  · intro b _ hb
    rw [UpperUnipotent.entry_eq_zero u (lt_of_le_of_ne (Fin.le_last b) hb), zero_mul]
  · simp

variable {k}

/-- The quotient integral of `Θ(lastRow) F` against the last-row fibers. -/
theorem integral_lastRow_eq (D : ComplexQuotientMeasureData (k + 1)) {c : ℝ≥0}
    (hμ : D.groupHaar = c • complexGeneralLinearHaar (k + 1 + 1)) {ρ : G → ℝ≥0}
    (hρ : IsNormalizingFunction N D.unipotentHaar (fun g => (ρ g : ℝ≥0∞))) {F : G → ℂ}
    (hFc : Continuous F) (hF : ∀ (u : N) (g : G), F (u.val * g) = F g)
    (hFi : Integrable (fun q : LeftUnipotentQuotient (k + 1) ℂ => F q.out) D.measure)
    {Θ : Row → ℂ} (hΘ : Measurable Θ) (hΘb : ∀ η, ‖Θ η‖ ≤ 1) :
    Integrable (fiber k F ρ) ∧
      ∫ q, Θ (lastRow k q.out) * F q.out ∂D.measure = (c : ℂ) * ∫ η, Θ η * fiber k F ρ η := by
  let := D.groupHaar_isHaar
  let := D.unipotentHaar_isHaar
  let := D.unipotentHaar_rightInvariant
  have hH : IsClosed (N : Set G) := UpperUnipotent.isClosed
  have hc : c ≠ 0 := by
    rintro rfl
    have h0 : D.groupHaar = 0 := by rw [hμ, zero_smul]
    exact (Measure.IsOpenPosMeasure.open_pos (μ := D.groupHaar) Set.univ isOpen_univ
      Set.univ_nonempty) (by rw [h0]; rfl)
  -- the integrand as a descended function
  let f : G → ℂ := fun g => Θ (lastRow k g) * F g
  have hfinv : ∀ (u : N) (g : G), f (u.val * g) = f g := by
    intro u g
    simp only [f, lastRow_unipotent_mul, hF]
  have hlast : Continuous (lastRow k) :=
    continuous_pi fun j => (GeneralLinear.entry (R := ℂ) (Fin.last (k + 1)) j).continuous
  have hfm : Measurable f := ((hΘ.comp hlast.measurable).mul hFc.measurable)
  have hdesc (φ : G → ℂ) (hφ : ∀ (u : N) (g : G), φ (u.val * g) = φ g) :
      (fun q : LeftUnipotentQuotient (k + 1) ℂ => φ q.out) = descend N φ hφ := by
    funext q
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  -- integrability on the group and on matrices
  have hFi' : Integrable (fun g => ((ρ g : ℝ≥0∞).toReal) • F g) D.groupHaar := by
    rw [hdesc F hF] at hFi
    exact (D.compatible.integrable_descend_iff hH hρ F hFc.measurable hF).mp hFi
  have hW : Integrable (weighted k F ρ) (complexGeneralLinearHaar (k + 1 + 1)) := by
    rw [hμ] at hFi'
    have := (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hc) ENNReal.coe_ne_top).mp hFi'
    refine this.congr (ae_of_all _ fun g => ?_)
    simp [weighted, Complex.real_smul]
  have hM : Integrable (matrixDensity (k + 1) (weighted k F ρ)) (matrixLebesgue (k + 1 + 1)) :=
    (integrable_complexGeneralLinearHaar_iff (k + 1) _).mp hW
  have hP : Integrable (fun p : Row × Rows =>
      matrixDensity (k + 1) (weighted k F ρ) (joinRows k p.1 p.2)) (volume.prod volume) :=
    (measurePreserving_joinRows k).integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ => Row) (Fin.last (k + 1))).symm.measurableEmbedding
      |>.mpr hM
  refine ⟨hP.integral_prod_left, ?_⟩
  -- the identity
  have hpt (X : Mat) : matrixDensity (k + 1) (fun g => ((ρ g : ℝ≥0∞).toReal) • f g) X =
      Θ (X (Fin.last (k + 1))) * matrixDensity (k + 1) (weighted k F ρ) X := by
    by_cases hX : X ∈ Set.range (Units.val : G → Mat)
    · obtain ⟨g, rfl⟩ := hX
      rw [matrixDensity_val, matrixDensity_val]
      simp only [f, weighted, lastRow, Complex.real_smul, ENNReal.coe_toReal]
      ring
    · rw [matrixDensity_of_not_mem _ _ hX, matrixDensity_of_not_mem _ _ hX, mul_zero]
  calc
    _ = ∫ q, descend N f hfinv q ∂D.measure := by rw [← hdesc f hfinv]
    _ = ∫ g, ((ρ g : ℝ≥0∞).toReal) • f g ∂D.groupHaar :=
      D.compatible.integral_descend_eq hH hρ f hfm hfinv
    _ = (c : ℂ) * ∫ g, ((ρ g : ℝ≥0∞).toReal) • f g ∂complexGeneralLinearHaar (k + 1 + 1) := by
      rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    _ = (c : ℂ) * ∫ X, Θ (X (Fin.last (k + 1))) * matrixDensity (k + 1) (weighted k F ρ) X
          ∂matrixLebesgue (k + 1 + 1) := by
      rw [integral_complexGeneralLinearHaar]
      simp_rw [hpt]
    _ = (c : ℂ) * ∫ η, Θ η * fiber k F ρ η := by
      congr 1
      rw [← (measurePreserving_joinRows k).integral_comp
        (MeasurableEquiv.piFinSuccAbove (fun _ => Row) (Fin.last (k + 1))).symm.measurableEmbedding]
      have hP' : Integrable (fun p : Row × Rows =>
          Θ (joinRows k p.1 p.2 (Fin.last (k + 1))) *
            matrixDensity (k + 1) (weighted k F ρ) (joinRows k p.1 p.2)) (volume.prod volume) := by
        refine hP.bdd_mul (c := 1) ?_ (ae_of_all _ fun p => hΘb _)
        exact (hΘ.comp ((measurable_pi_apply _).comp
          (MeasurableEquiv.piFinSuccAbove (fun _ => Row)
            (Fin.last (k + 1))).symm.measurable)).aestronglyMeasurable
      rw [integral_prod _ hP']
      simp only [joinRows_last]
      refine integral_congr_ae (ae_of_all _ fun η => ?_)
      exact integral_const_mul _ _

variable (k)

/-- Right multiplication of each first row by a matrix. -/
def rowsMul (B : Mat) (A : Rows) : Rows := fun i => Matrix.vecMul (A i) B

theorem joinRows_mul (η : Row) (A : Rows) (B : Mat) :
    joinRows k η A * B = joinRows k (Matrix.vecMul η B) (rowsMul k B A) := by
  ext i j
  refine Fin.lastCases ?_ (fun i₀ => ?_) i
  · simp only [Matrix.mul_apply, joinRows_last, Matrix.vecMul, dotProduct]
  · simp only [Matrix.mul_apply, joinRows_castSucc, rowsMul, Matrix.vecMul, dotProduct]

/-- The last standard basis row. -/
def lastBasis : Row := Pi.single (Fin.last (k + 1)) 1

theorem lastBasis_vecMul (g : G) : Matrix.vecMul (lastBasis k) g.val = lastRow k g := by
  funext j
  simp [lastBasis, lastRow]

private theorem map_rowsMul (g : G) :
    (volume : Measure Rows).map (rowsMul k g.val) =
      (ENNReal.ofReal ((‖g.val.det‖ ^ 2)⁻¹)) ^ (k + 1) • (volume : Measure Rows) := by
  have hB : g.val.det ≠ 0 := g.det_ne_zero
  let e := Langlands.Archimedean.ComplexPartialJacquet.vecMulEquiv hB
  have he : (volume : Measure Row).map e = ENNReal.ofReal ((‖g.val.det‖ ^ 2)⁻¹) • volume :=
    Langlands.Archimedean.ComplexPartialJacquet.map_vecMulEquiv hB
  have hr : rowsMul k g.val = fun (A : Rows) i => e (A i) := rfl
  rw [hr, show (volume : Measure Rows) = Measure.pi (fun _ : Fin (k + 1) => (volume : Measure Row))
    from rfl, Measure.pi_map_pi (hμ := fun _ => e.sigmaFinite_map) (fun _ => e.measurable.aemeasurable)]
  have he' : (volume : Measure Row).map e = ((‖g.val.det‖ ^ 2)⁻¹).toNNReal • volume := by
    rw [he]
    rfl
  simp_rw [he']
  rw [Langlands.HarmonicAnalysis.pi_nnreal_smul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.smul_def, ENNReal.coe_pow]
  rfl

theorem integral_rowsMul (g : G) (φ : Rows → ℂ) :
    ∫ A, φ (rowsMul k g.val A) = ((‖g.val.det‖ ^ 2)⁻¹ ^ (k + 1) : ℝ) • ∫ A, φ A := by
  have hB : g.val.det ≠ 0 := g.det_ne_zero
  let e : Rows ≃ᵐ Rows := MeasurableEquiv.piCongrRight
    (fun _ => Langlands.Archimedean.ComplexPartialJacquet.vecMulEquiv hB)
  have he : (e : Rows → Rows) = rowsMul k g.val := by
    funext A
    rfl
  rw [← he, ← e.measurableEmbedding.integral_map, he, map_rowsMul, integral_smul_measure]
  congr 1
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

theorem matrixDensity_mul (f : G → ℂ) (X : Mat) (g : G) :
    matrixDensity (k + 1) f (X * g.val) =
      ((‖g.val.det‖ ^ 2)⁻¹ ^ (k + 1 + 1) : ℝ) • matrixDensity (k + 1) (fun x => f (x * g)) X := by
  by_cases hX : X ∈ Set.range (Units.val : G → Mat)
  · obtain ⟨x, rfl⟩ := hX
    rw [← Units.val_mul, matrixDensity_val, matrixDensity_val, smul_smul]
    congr 1
    simp only [matrixWeight, normSqHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Units.val_mul,
      Matrix.det_mul, NNReal.coe_pow, NNReal.coe_inv, nnnorm_mul, mul_pow, mul_inv, coe_nnnorm,
      NNReal.coe_mul]
    ring
  · have hX' : X * g.val ∉ Set.range (Units.val : G → Mat) := by
      rintro ⟨y, hy⟩
      apply hX
      refine ⟨y * g⁻¹, ?_⟩
      rw [Units.val_mul, hy, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
    rw [matrixDensity_of_not_mem _ _ hX, matrixDensity_of_not_mem _ _ hX', smul_zero]

/-- Translating the fiber point by a group element translates the function and the
normalizing function. -/
theorem fiber_lastRow (F : G → ℂ) (ρ : G → ℝ≥0) (g : G) :
    fiber k F ρ (lastRow k g) =
      ((‖g.val.det‖ ^ 2)⁻¹ : ℝ) • fiber k (fun x => F (x * g)) (fun x => ρ (x * g)) (lastBasis k) := by
  have hdet : 0 < ‖g.val.det‖ ^ 2 := by
    have := g.det_ne_zero
    positivity
  have h := integral_rowsMul k g (fun A => matrixDensity (k + 1) (weighted k F ρ)
    (joinRows k (lastRow k g) A))
  have hrw (A : Rows) : matrixDensity (k + 1) (weighted k F ρ) (joinRows k (lastRow k g)
      (rowsMul k g.val A)) = ((‖g.val.det‖ ^ 2)⁻¹ ^ (k + 1 + 1) : ℝ) •
        matrixDensity (k + 1) (weighted k (fun x => F (x * g)) (fun x => ρ (x * g)))
          (joinRows k (lastBasis k) A) := by
    rw [← lastBasis_vecMul, ← joinRows_mul, matrixDensity_mul]
    rfl
  simp_rw [hrw] at h
  rw [integral_smul] at h
  unfold fiber
  have hne : ((‖g.val.det‖ ^ 2)⁻¹ ^ (k + 1) : ℝ) ≠ 0 := by positivity
  rw [← inv_smul_eq_iff₀ hne] at h
  rw [← h, smul_smul]
  congr 1
  field_simp
  ring

end Fiber

section Block

variable (k : ℕ)

local notation "G" => Langlands.GeneralLinear (k + 1 + 1) ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (k + 1 + 1) ℂ
local notation "G₁" => Langlands.GeneralLinear (k + 1) ℂ
local notation "N₁" => Langlands.GeneralLinear.upperUnipotent (k + 1) ℂ
local notation "Mat" => Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ
local notation "Mat₁" => Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ
local notation "Row" => Fin (k + 1 + 1) → ℂ
local notation "Rows" => Fin (k + 1) → Fin (k + 1 + 1) → ℂ
local notation "Col" => Fin (k + 1) → ℂ

/-- Splitting the first rows into their last column and their leading square block. -/
def splitRows : Rows ≃ᵐ Col × (Fin (k + 1) → Fin (k + 1) → ℂ) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin (k + 1) =>
    MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last (k + 1)))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℂ (Fin (k + 1) → ℂ) (Fin (k + 1)))

theorem measurePreserving_splitRows :
    MeasurePreserving (splitRows k) (volume : Measure Rows)
      ((volume : Measure Col).prod (volume : Measure (Fin (k + 1) → Fin (k + 1) → ℂ))) :=
  (measurePreserving_arrowProdEquivProdArrow ℂ (Fin (k + 1) → ℂ) (Fin (k + 1))
    (fun _ => volume) (fun _ => volume)).comp
    (measurePreserving_pi (fun _ => volume) (fun _ => (volume : Measure ℂ).prod volume)
      (fun _ => measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1 + 1) => (volume : Measure ℂ))
        (Fin.last (k + 1))))

/-- The first rows `(h | u)`. -/
def blockRows (p : Col × (Fin (k + 1) → Fin (k + 1) → ℂ)) : Rows :=
  fun i => Fin.snoc (α := fun _ => ℂ) (p.2 i) (p.1 i)

theorem splitRows_symm (p : Col × (Fin (k + 1) → Fin (k + 1) → ℂ)) :
    (splitRows k).symm p = blockRows k p := by
  rw [MeasurableEquiv.symm_apply_eq]
  refine Prod.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
  · change p.1 i = Fin.snoc (α := fun _ => ℂ) (p.2 i) (p.1 i) (Fin.last (k + 1))
    simp
  · change p.2 i j = Fin.snoc (α := fun _ => ℂ) (p.2 i) (p.1 i) ((Fin.last (k + 1)).succAbove j)
    simp

/-- The matrix `[[h, u], [0, 1]]`. -/
def blockMatrix (p : Col × (Fin (k + 1) → Fin (k + 1) → ℂ)) : Mat :=
  joinRows k (lastBasis k) (blockRows k p)

theorem blockMatrix_castSucc_castSucc (u : Col) (h : Mat₁) (i j : Fin (k + 1)) :
    blockMatrix k (u, h) i.castSucc j.castSucc = h i j := by
  simp [blockMatrix, blockRows]

theorem blockMatrix_castSucc_last (u : Col) (h : Mat₁) (i : Fin (k + 1)) :
    blockMatrix k (u, h) i.castSucc (Fin.last (k + 1)) = u i := by
  simp [blockMatrix, blockRows]

theorem blockMatrix_last (u : Col) (h : Mat₁) (j : Fin (k + 1 + 1)) :
    blockMatrix k (u, h) (Fin.last (k + 1)) j = lastBasis k j := by
  simp [blockMatrix]

theorem continuous_blockMatrix : Continuous (blockMatrix k) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun p : Col × (Fin (k + 1) → Fin (k + 1) → ℂ) => blockMatrix k (p.1, p.2) i j
  refine Fin.lastCases ?_ (fun i₀ => ?_) i
  · simp only [blockMatrix_last]
    exact continuous_const
  · refine Fin.lastCases ?_ (fun j₀ => ?_) j
    · simp only [blockMatrix_castSucc_last]
      exact (continuous_apply i₀).comp continuous_fst
    · simp only [blockMatrix_castSucc_castSucc]
      exact (continuous_apply j₀).comp ((continuous_apply i₀).comp continuous_snd)

/-- The leading block inclusion `h ↦ diag(h, 1)`. -/
abbrev pad₁ : G₁ →* G := padGL (Nat.le_succ (k + 1))

variable {k}

theorem pad₁_cc (h : G₁) (i j : Fin (k + 1)) : (pad₁ k h).val i.castSucc j.castSucc = h.val i j := by
  rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨i.isLt, j.isLt⟩]
  rfl

theorem pad₁_cl (h : G₁) (i : Fin (k + 1)) : (pad₁ k h).val i.castSucc (Fin.last (k + 1)) = 0 := by
  rw [UnequalAnalytic.padGL_col _ _ _ (by simp)]
  exact Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne

theorem pad₁_lc (h : G₁) (j : Fin (k + 1)) : (pad₁ k h).val (Fin.last (k + 1)) j.castSucc = 0 := by
  rw [UnequalAnalytic.padGL_row _ _ _ (by simp)]
  exact Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne'

theorem pad₁_ll (h : G₁) : (pad₁ k h).val (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := by
  rw [UnequalAnalytic.padGL_row _ _ _ (by simp)]
  exact Matrix.one_apply_eq _

theorem lastBasis_castSucc (j : Fin (k + 1)) : lastBasis k j.castSucc = 0 := by
  simp [lastBasis, (Fin.castSucc_lt_last j).ne]

theorem lastBasis_last : lastBasis k (Fin.last (k + 1)) = 1 := by
  simp [lastBasis]

theorem blockMatrix_mul_pad (u : Col) (A : Mat₁) (h : G₁) :
    blockMatrix k (u, A) * (pad₁ k h).val = blockMatrix k (u, A * h.val) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun j₀ => ?_) j
  · simp only [pad₁_cl, pad₁_ll, mul_zero, Finset.sum_const_zero, mul_one, zero_add]
    refine Fin.lastCases ?_ (fun i₀ => ?_) i
    · rw [blockMatrix_last, blockMatrix_last]
    · rw [blockMatrix_castSucc_last, blockMatrix_castSucc_last]
  · simp only [pad₁_cc, pad₁_lc, mul_zero, add_zero]
    refine Fin.lastCases ?_ (fun i₀ => ?_) i
    · simp only [blockMatrix_last, lastBasis_castSucc, zero_mul, Finset.sum_const_zero]
    · simp only [blockMatrix_castSucc_castSucc, Matrix.mul_apply]

theorem pad₁_mul_blockMatrix (g : G₁) (u : Col) (A : Mat₁) :
    (pad₁ k g).val * blockMatrix k (u, A) = blockMatrix k (g.val.mulVec u, g.val * A) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i₀ => ?_) i
  · simp only [pad₁_lc, pad₁_ll, zero_mul, Finset.sum_const_zero, one_mul, zero_add,
      blockMatrix_last]
  · simp only [pad₁_cc, pad₁_cl, zero_mul, add_zero]
    refine Fin.lastCases ?_ (fun j₀ => ?_) j
    · simp only [blockMatrix_castSucc_last, Matrix.mulVec, dotProduct]
    · simp only [blockMatrix_castSucc_castSucc, Matrix.mul_apply]

theorem blockJoin_val (n' : N₁) (u : Col) :
    (ComplexJacquet.complexUnipotentBlockJoin (k + 1) (n', u)).val.val = blockMatrix k (u, n'.val.val) := by
  ext i j
  refine Fin.lastCases ?_ (fun i₀ => ?_) i
  · rw [blockMatrix_last]
    refine Fin.lastCases ?_ (fun j₀ => ?_) j
    · rw [lastBasis_last]
      exact UpperUnipotent.entry_diag _ _
    · rw [lastBasis_castSucc]
      exact UpperUnipotent.entry_eq_zero _ (Fin.castSucc_lt_last j₀)
  · refine (congrFun (congrFun (ComplexJacquet.complexUnipotentBlockJoin_rectangle n' u) i₀) j).trans ?_
    refine Fin.lastCases ?_ (fun j₀ => ?_) j
    · rw [rectangularJoin_last, blockMatrix_castSucc_last]
    · rw [rectangularJoin_castSucc, blockMatrix_castSucc_castSucc]

theorem det_blockMatrix (u : Col) (A : Mat₁) : (blockMatrix k (u, A)).det = A.det := by
  rw [Matrix.det_succ_row _ (Fin.last (k + 1)), Finset.sum_eq_single (Fin.last (k + 1))]
  · rw [blockMatrix_last, lastBasis_last, mul_one]
    have hsub : (blockMatrix k (u, A)).submatrix (Fin.last (k + 1)).succAbove
        (Fin.last (k + 1)).succAbove = A := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, blockMatrix_castSucc_castSucc]
    rw [hsub, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  · intro j _ hj
    rw [blockMatrix_last]
    simp [lastBasis, hj]
  · simp

/-- The unipotent element `[[1, u], [0, 1]]`. -/
abbrev colUnip (u : Col) : N := ComplexJacquet.complexUnipotentBlockJoin (k + 1) (1, u)

theorem blockMatrix_val (u : Col) (h : G₁) :
    blockMatrix k (u, h.val) = ((colUnip u).val * pad₁ k h).val := by
  rw [Units.val_mul, blockJoin_val, blockMatrix_mul_pad]
  simp

theorem blockJoin_eq (n' : N₁) (u : Col) :
    (ComplexJacquet.complexUnipotentBlockJoin (k + 1) (n', u)).val = (colUnip u).val * pad₁ k n'.val := by
  apply Units.ext
  rw [blockJoin_val, Units.val_mul, blockJoin_val, blockMatrix_mul_pad]
  simp

theorem blockMatrix_mem_range_iff (u : Col) (A : Mat₁) :
    blockMatrix k (u, A) ∈ Set.range (Units.val : G → Mat) ↔
      A ∈ Set.range (Units.val : G₁ → Mat₁) := by
  have h₁ : ∀ {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ),
      X ∈ Set.range (Units.val : Langlands.GeneralLinear n ℂ → Matrix (Fin n) (Fin n) ℂ) ↔
        IsUnit X.det := by
    intro n X
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, hg⟩⟩
  rw [h₁, h₁, det_blockMatrix]

theorem det_colUnip_mul_pad (u : Col) (h : G₁) :
    ((colUnip u).val * pad₁ k h).val.det = h.val.det := by
  rw [Units.val_mul, Matrix.det_mul, Langlands.RankinSelberg.unipotent_det, one_mul,
    UnequalAnalytic.det_padGL]

theorem pad₁_mem (n' : N₁) : pad₁ k n'.val ∈ N := by
  rw [← mul_one (pad₁ k n'.val)]
  have h := (ComplexJacquet.complexUnipotentBlockJoin (k + 1) (n', 0)).property
  rw [blockJoin_eq] at h
  have h0 : colUnip (k := k) 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [blockJoin_val]
    ext i j
    refine Fin.lastCases ?_ (fun i₀ => ?_) i <;> refine Fin.lastCases ?_ (fun j₀ => ?_) j
    · simp [blockMatrix_last, lastBasis_last]
    · simp [blockMatrix_last, lastBasis_castSucc, (Fin.castSucc_lt_last j₀).ne']
    · simp [blockMatrix_castSucc_last, (Fin.castSucc_lt_last i₀).ne]
    · simp [blockMatrix_castSucc_castSucc, Matrix.one_apply]
  rw [h0] at h
  simpa using h

variable (k) in
/-- Integral of a normalizing function along the last column of `[[1, u], [0, 1]] diag(h, 1)`. -/
def columnMass (ρ : G → ℝ≥0) (h : G₁) : ℝ≥0∞ :=
  ∫⁻ u : Col, (ρ ((colUnip u).val * pad₁ k h) : ℝ≥0∞)

private theorem measurable_colUnip : Measurable (fun u : Col => (colUnip (k := k) u).val) :=
  continuous_subtype_val.measurable.comp
    ((ComplexJacquet.complexUnipotentBlockJoin (k + 1)).measurable.comp
      (measurable_const.prodMk measurable_id))

private theorem measurable_columnIntegrand {ρ : G → ℝ≥0} (hρ : Measurable ρ) :
    Measurable (fun p : G₁ × Col => (ρ ((colUnip p.2).val * pad₁ k p.1) : ℝ≥0∞)) := by
  have hpad : Continuous (pad₁ k) := UnequalAnalytic.continuous_padGL _
  exact measurable_coe_nnreal_ennreal.comp (hρ.comp
    ((measurable_colUnip.comp measurable_snd).mul (hpad.measurable.comp measurable_fst)))

theorem measurable_columnMass {ρ : G → ℝ≥0} (hρ : Measurable ρ) :
    Measurable (columnMass k ρ) :=
  (measurable_columnIntegrand hρ).lintegral_prod_right'

/-- The column mass, scaled by the block Haar constant, is a normalizing function for the
smaller unipotent group. -/
theorem isNormalizing_columnMass (D : ComplexQuotientMeasureData (k + 1))
    (D' : ComplexQuotientMeasureData k) {cN : ℝ≥0}
    (hN : D.unipotentHaar = cN • (D'.unipotentHaar.prod (volume : Measure Col)).map
      (ComplexJacquet.complexUnipotentBlockJoin (k + 1)))
    {ρ : G → ℝ≥0} (hρm : Measurable ρ)
    (hρ : IsNormalizingFunction N D.unipotentHaar (fun g => (ρ g : ℝ≥0∞))) :
    IsNormalizingFunction N₁ D'.unipotentHaar (fun h => (cN : ℝ≥0∞) * columnMass k ρ h) := by
  let := D'.unipotentHaar_isHaar
  refine ⟨(measurable_columnMass hρm).const_mul _, fun h => ?_⟩
  have hpadmul (n' : N₁) (u : Col) :
      (colUnip u).val * pad₁ k (n'.val * h) =
        (ComplexJacquet.complexUnipotentBlockJoin (k + 1) (n', u)).val * pad₁ k h := by
    rw [blockJoin_eq n' u, map_mul, mul_assoc]
  have hm : Measurable (fun n : N => (ρ (n.val * pad₁ k h) : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (hρm.comp
      (continuous_subtype_val.measurable.mul_const _))
  have hone := hρ.lintegral_eq_one (pad₁ k h)
  have hm' : Measurable (fun a : N₁ × Col =>
      (ρ ((ComplexJacquet.complexUnipotentBlockJoin (k + 1) a).val * pad₁ k h) : ℝ≥0∞)) :=
    hm.comp (ComplexJacquet.complexUnipotentBlockJoin (k + 1)).measurable
  rw [hN, lintegral_smul_measure,
    lintegral_map hm (ComplexJacquet.complexUnipotentBlockJoin (k + 1)).measurable,
    lintegral_prod _ hm'.aemeasurable] at hone
  rw [lintegral_const_mul (f := fun n' : N₁ => columnMass k ρ (n'.val * h)) _
    ((measurable_columnMass hρm).comp (continuous_subtype_val.measurable.mul_const h))]
  simp only [columnMass, hpadmul]
  rw [← hone, ENNReal.smul_def, smul_eq_mul]

/-- The lower integrand `|det h|⁻¹ F(diag(h, 1))`. -/
def lowerFunction (F : G → ℂ) (h : G₁) : ℂ := ((‖h.val.det‖ ^ 2)⁻¹ : ℝ) • F (pad₁ k h)

theorem lowerFunction_unipotent_mul {F : G → ℂ} (hF : ∀ (u : N) (g : G), F (u.val * g) = F g)
    (n' : N₁) (h : G₁) : lowerFunction F (n'.val * h) = lowerFunction F h := by
  simp only [lowerFunction, map_mul, Units.val_mul, Matrix.det_mul,
    Langlands.RankinSelberg.unipotent_det, one_mul]
  rw [hF ⟨pad₁ k n'.val, pad₁_mem n'⟩]

theorem continuous_lowerFunction {F : G → ℂ} (hF : Continuous F) :
    Continuous (lowerFunction (k := k) F) := by
  have hdet : Continuous (fun h : G₁ => h.val.det) :=
    continuous_id.matrix_det.comp Units.continuous_val
  have hinv : Continuous (fun h : G₁ => ((‖h.val.det‖ ^ 2)⁻¹ : ℝ)) :=
    (hdet.norm.pow 2).inv₀ (fun h => pow_ne_zero 2 (norm_ne_zero_iff.mpr h.det_ne_zero))
  exact hinv.smul (hF.comp (UnequalAnalytic.continuous_padGL _))

theorem matrixWeight_colUnip_mul_pad (u : Col) (h : G₁) :
    (matrixWeight (k + 1 + 1) normSqHom ((colUnip u).val * pad₁ k h).val : ℝ) =
      (matrixWeight (k + 1) normSqHom h.val : ℝ) * (‖h.val.det‖ ^ 2)⁻¹ := by
  simp only [matrixWeight, det_colUnip_mul_pad, normSqHom, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, NNReal.coe_pow, NNReal.coe_inv, coe_nnnorm]
  ring

theorem matrixDensity_smul (n : ℕ) (c : ℝ) (f : Langlands.GeneralLinear (n + 1) ℂ → ℂ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    matrixDensity n (fun g => c • f g) X = c • matrixDensity n f X := by
  by_cases hX : X ∈ Set.range (Units.val : Langlands.GeneralLinear (n + 1) ℂ → _)
  · obtain ⟨g, rfl⟩ := hX
    rw [matrixDensity_val, matrixDensity_val, smul_comm]
  · rw [matrixDensity_of_not_mem _ _ hX, matrixDensity_of_not_mem _ _ hX, smul_zero]

private theorem integral_columnMass {ρ : G → ℝ≥0} (hρ : Measurable ρ) (h : G₁) :
    ∫ u : Col, ((ρ ((colUnip u).val * pad₁ k h) : ℝ) : ℂ) = ((columnMass k ρ h).toReal : ℂ) := by
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun u => NNReal.coe_nonneg _)]
  · simp only [ENNReal.ofReal_coe_nnreal, columnMass]
  · exact (NNReal.continuous_coe.measurable.comp (hρ.comp
      (measurable_colUnip.mul_const _))).aestronglyMeasurable

theorem integral_blockMatrix {F : G → ℂ} (hF : ∀ (u : N) (g : G), F (u.val * g) = F g)
    {ρ : G → ℝ≥0} (hρ : Measurable ρ) (h : Fin (k + 1) → Fin (k + 1) → ℂ) :
    ∫ u : Col, matrixDensity (k + 1) (weighted k F ρ) (blockMatrix k (u, h)) =
      matrixDensity k (fun h₀ => (columnMass k ρ h₀).toReal • lowerFunction F h₀) h := by
  by_cases hh : h ∈ Set.range (Units.val : G₁ → Mat₁)
  · obtain ⟨h₀, rfl⟩ := hh
    simp_rw [blockMatrix_val, matrixDensity_val, weighted, hF (colUnip _),
      matrixWeight_colUnip_mul_pad]
    rw [integral_smul, integral_mul_const]
    rw [integral_columnMass hρ, lowerFunction]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  · have hb (u : Col) : blockMatrix k (u, h) ∉ Set.range (Units.val : G → Mat) := by
      rw [blockMatrix_mem_range_iff]
      exact hh
    simp_rw [matrixDensity_of_not_mem _ _ (hb _)]
    rw [integral_zero, matrixDensity_of_not_mem _ _ hh]

private theorem enorm_nnreal_complex (x : ℝ≥0) : ‖((x : ℝ) : ℂ)‖ₑ = (x : ℝ≥0∞) := by
  rw [← ofReal_norm, show ‖((x : ℝ) : ℂ)‖ = x by simp, ENNReal.ofReal_coe_nnreal]

theorem lintegral_enorm_blockMatrix {F : G → ℂ} (hF : ∀ (u : N) (g : G), F (u.val * g) = F g)
    {ρ : G → ℝ≥0} (h : Fin (k + 1) → Fin (k + 1) → ℂ) :
    ∫⁻ u : Col, ‖matrixDensity (k + 1) (weighted k F ρ) (blockMatrix k (u, h))‖ₑ =
      (matrixWeight (k + 1) normSqHom h : ℝ≥0∞) *
        Function.extend Units.val (fun h₀ : G₁ => ‖lowerFunction F h₀‖ₑ * columnMass k ρ h₀) 0 h := by
  by_cases hh : h ∈ Set.range (Units.val : G₁ → Mat₁)
  · obtain ⟨h₀, rfl⟩ := hh
    simp_rw [blockMatrix_val, matrixDensity_val, weighted, hF (colUnip _),
      matrixWeight_colUnip_mul_pad, enorm_smul, enorm_mul]
    rw [Units.val_injective.extend_apply, lowerFunction, enorm_smul, columnMass]
    simp_rw [enorm_nnreal_complex]
    have hw : ‖((matrixWeight (k + 1) normSqHom h₀.val : ℝ≥0) : ℝ)‖ₑ =
        (matrixWeight (k + 1) normSqHom h₀.val : ℝ≥0∞) := by
      rw [Real.enorm_of_nonneg (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    have hre (u : Col) :
        ‖((matrixWeight (k + 1) normSqHom h₀.val : ℝ≥0) : ℝ)‖ₑ * ‖(‖h₀.val.det‖ ^ 2)⁻¹‖ₑ *
          ((ρ ((colUnip u).val * pad₁ k h₀) : ℝ≥0∞) * ‖F (pad₁ k h₀)‖ₑ) =
        ((matrixWeight (k + 1) normSqHom h₀.val : ℝ≥0∞) * ‖(‖h₀.val.det‖ ^ 2)⁻¹‖ₑ *
          ‖F (pad₁ k h₀)‖ₑ) * (ρ ((colUnip u).val * pad₁ k h₀) : ℝ≥0∞) := by
      rw [hw]
      ring
    simp_rw [hre]
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      enorm_ne_top) enorm_ne_top)]
    ring
  · have hb (u : Col) : blockMatrix k (u, h) ∉ Set.range (Units.val : G → Mat) := by
      rw [blockMatrix_mem_range_iff]
      exact hh
    simp_rw [matrixDensity_of_not_mem _ _ (hb _), enorm_zero, lintegral_zero]
    rw [Function.extend_apply' _ _ _ (by simpa using hh), Pi.zero_apply, mul_zero]

/-- At the standard last row, the fiber is a fixed positive multiple of the quotient
integral of the lower function over the smaller unipotent quotient. -/
theorem fiber_lastBasis (D : ComplexQuotientMeasureData (k + 1)) (D' : ComplexQuotientMeasureData k)
    {c' : ℝ≥0} (hμ' : D'.groupHaar = c' • complexGeneralLinearHaar (k + 1))
    {cN : ℝ≥0} (hcN : cN ≠ 0)
    (hN : D.unipotentHaar = cN • (D'.unipotentHaar.prod (volume : Measure Col)).map
      (ComplexJacquet.complexUnipotentBlockJoin (k + 1)))
    {ρ : G → ℝ≥0} (hρm : Measurable ρ)
    (hρ : IsNormalizingFunction N D.unipotentHaar (fun g => (ρ g : ℝ≥0∞)))
    {F : G → ℂ} (hFc : Continuous F) (hF : ∀ (u : N) (g : G), F (u.val * g) = F g)
    (hFi : Integrable (fun q : LeftUnipotentQuotient k ℂ => lowerFunction F q.out) D'.measure) :
    fiber k F ρ (lastBasis k) =
      (((c' * cN : ℝ≥0) : ℝ)⁻¹ : ℝ) • ∫ q, lowerFunction F q.out ∂D'.measure := by
  let := D'.groupHaar_isHaar
  let := D'.unipotentHaar_isHaar
  let := D'.unipotentHaar_rightInvariant
  have hH : IsClosed (N₁ : Set G₁) := UpperUnipotent.isClosed
  have hc' : c' ≠ 0 := by
    rintro rfl
    have h0 : D'.groupHaar = 0 := by rw [hμ', zero_smul]
    exact (Measure.IsOpenPosMeasure.open_pos (μ := D'.groupHaar) Set.univ isOpen_univ
      Set.univ_nonempty) (by rw [h0]; rfl)
  have hR := isNormalizing_columnMass D D' hN hρm hρ
  have hLc : Continuous (lowerFunction (k := k) F) := continuous_lowerFunction hFc
  have hLinv : ∀ (n' : N₁) (h : G₁), lowerFunction F (n'.val * h) = lowerFunction F h :=
    lowerFunction_unipotent_mul hF
  have hdesc (φ : G₁ → ℂ) (hφ : ∀ (n' : N₁) (h : G₁), φ (n'.val * h) = φ h) :
      (fun q : LeftUnipotentQuotient k ℂ => φ q.out) = descend N₁ φ hφ := by
    funext q
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  -- the quotient side
  have hpt (X : Mat₁) : matrixDensity k (fun h => (((cN : ℝ≥0∞) * columnMass k ρ h).toReal) •
      lowerFunction F h) X = (cN : ℝ) • matrixDensity k (fun h => (columnMass k ρ h).toReal •
        lowerFunction F h) X := by
    rw [← matrixDensity_smul]
    congr 1
    funext h
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, smul_smul]
  have hQ : ∫ q, lowerFunction F q.out ∂D'.measure = ((c' * cN : ℝ≥0) : ℝ) •
      ∫ X, matrixDensity k (fun h => (columnMass k ρ h).toReal • lowerFunction F h) X
        ∂matrixLebesgue (k + 1) := by
    rw [hdesc _ hLinv, D'.compatible.integral_descend_eq hH hR _ hLc.measurable hLinv, hμ',
      integral_smul_nnreal_measure, integral_complexGeneralLinearHaar]
    simp_rw [hpt]
    rw [integral_smul, NNReal.smul_def, smul_smul, NNReal.coe_mul]
  -- integrability of the block integrand
  have hmeas : Measurable (fun p : Col × (Fin (k + 1) → Fin (k + 1) → ℂ) =>
      matrixDensity (k + 1) (weighted k F ρ) (blockMatrix k p)) :=
    (measurable_matrixDensity (k + 1) (by
      unfold weighted
      exact (Complex.measurable_ofReal.comp (NNReal.continuous_coe.measurable.comp hρm)).mul
        hFc.measurable)).comp (continuous_blockMatrix k).measurable
  have hLm : Measurable (fun h : G₁ => ‖lowerFunction F h‖ₑ * columnMass k ρ h) :=
    hLc.enorm.measurable.mul (measurable_columnMass hρm)
  have hfin : ∫⁻ h : G₁, ‖lowerFunction F h‖ₑ * columnMass k ρ h ∂complexGeneralLinearHaar (k + 1) ≠ ⊤ := by
    have h1 := D'.compatible.lintegral_descend_eq hH hR (fun h => ‖lowerFunction F h‖ₑ)
      hLc.enorm.measurable (fun n' h => by rw [hLinv])
    rw [hμ', lintegral_smul_measure] at h1
    have h2 : ∫⁻ q, descend N₁ (fun h => ‖lowerFunction F h‖ₑ) (fun n' h => by rw [hLinv]) q
        ∂D'.measure < ⊤ := by
      have hfi := hFi.2
      rw [hdesc _ hLinv] at hfi
      refine lt_of_eq_of_lt (lintegral_congr fun q => ?_) hfi
      induction q using Quotient.inductionOn with
      | h g => rfl
    intro htop
    have h3 : ∫⁻ h : G₁, ‖lowerFunction F h‖ₑ * ((cN : ℝ≥0∞) * columnMass k ρ h)
        ∂complexGeneralLinearHaar (k + 1) = ⊤ := by
      simp_rw [mul_left_comm _ (cN : ℝ≥0∞)]
      rw [lintegral_const_mul _ hLm, htop, ENNReal.mul_top (by simpa using hcN)]
    rw [h1, h3, ENNReal.smul_def, smul_eq_mul, ENNReal.mul_top (ENNReal.coe_ne_zero.mpr hc')] at h2
    exact lt_irrefl _ h2
  have hint : Integrable (fun p : Col × (Fin (k + 1) → Fin (k + 1) → ℂ) =>
      matrixDensity (k + 1) (weighted k F ρ) (blockMatrix k p)) (volume.prod volume) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod_symm _ hmeas.enorm.aemeasurable]
    simp_rw [lintegral_enorm_blockMatrix hF]
    have := lintegral_complexGeneralLinearHaar k _ hLm
    change ∫⁻ h, _ ∂matrixLebesgue (k + 1) < ⊤
    rw [← this]
    exact lt_top_iff_ne_top.mpr hfin
  -- the fiber side
  have hfib : fiber k F ρ (lastBasis k) =
      ∫ X, matrixDensity k (fun h => (columnMass k ρ h).toReal • lowerFunction F h) X
        ∂matrixLebesgue (k + 1) := by
    unfold fiber
    rw [← ((measurePreserving_splitRows k).symm _).integral_comp
      (splitRows k).symm.measurableEmbedding]
    simp_rw [splitRows_symm]
    change ∫ p, matrixDensity (k + 1) (weighted k F ρ) (blockMatrix k p) ∂(volume.prod volume) = _
    rw [integral_prod_symm _ hint]
    simp_rw [integral_blockMatrix hF hρm]
    rfl
  rw [hfib, hQ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast mul_ne_zero hc' hcN), one_smul]

end Block

section Main

variable (k : ℕ)

local notation "G" => Langlands.GeneralLinear (k + 1 + 1) ℂ
local notation "Row" => Fin (k + 1 + 1) → ℂ

private theorem pi_selfDual_one :
    (Measure.pi fun _ : Fin (k + 1) => (complexSelfDualMeasure 1).measure) =
      ((2 : ℝ≥0) ^ (k + 1)) • (volume : Measure (Fin (k + 1) → ℂ)) := by
  have h : (complexSelfDualMeasure 1).measure = (2 : ℝ≥0) • (volume : Measure ℂ) := by
    simp [complexSelfDualMeasure]
  rw [h, Langlands.HarmonicAnalysis.pi_nnreal_smul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rfl

/-- **The last-row fiber of the complex unipotent quotient.** For compatible quotient
measures in two consecutive ranks there are positive constants such that every continuous
left-invariant function `F` integrable on `N_(k+2) \ GL_(k+2)(ℂ)` has an integrable density `Ψ`
of its last-row pushforward, and the value of `Ψ` at the last row of `g` is the integral of
`|det h|⁻¹ F(diag(h, 1) g)` over `N_(k+1) \ GL_(k+1)(ℂ)` up to the factor `|det g|⁻¹`. -/
theorem lastRowFiber (D : ComplexQuotientMeasureData (k + 1)) (D' : ComplexQuotientMeasureData k) :
    ∃ c₀ c : ℝ, 0 < c₀ ∧ 0 < c ∧ ∀ F : G → ℂ, Continuous F →
      (∀ (u : Langlands.GeneralLinear.upperUnipotent (k + 1 + 1) ℂ) (g : G), F (u.val * g) = F g) →
      Integrable (fun q : LeftUnipotentQuotient (k + 1) ℂ => F q.out) D.measure →
      ∃ Ψ : Row → ℂ, Integrable Ψ ∧
        (∀ Θ : Row → ℂ, Measurable Θ → (∀ η, ‖Θ η‖ ≤ 1) →
          ∫ q, Θ (lastRow k q.out) * F q.out ∂D.measure = (c₀ : ℂ) * ∫ η, Θ η * Ψ η) ∧
        ∀ g : G, Integrable (fun q : LeftUnipotentQuotient k ℂ =>
            lowerFunction (fun x => F (x * g)) q.out) D'.measure →
          Ψ (lastRow k g) = ((‖g.val.det‖ ^ 2)⁻¹ * c : ℝ) •
            ∫ q, lowerFunction (fun x => F (x * g)) q.out ∂D'.measure := by
  let := D.groupHaar_isHaar
  let := D.unipotentHaar_isHaar
  let := D.unipotentHaar_rightInvariant
  let := D'.groupHaar_isHaar
  let := D'.unipotentHaar_isHaar
  obtain ⟨ρ, hρc, hρ, -⟩ := exists_continuous_isNormalizingFunction
    (Langlands.GeneralLinear.upperUnipotent (k + 1 + 1) ℂ) UpperUnipotent.isClosed D.unipotentHaar
  let c₀ := Measure.haarScalarFactor D.groupHaar (complexGeneralLinearHaar (k + 1 + 1))
  have hμ : D.groupHaar = c₀ • complexGeneralLinearHaar (k + 1 + 1) :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hc₀ : 0 < c₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  let c' := Measure.haarScalarFactor D'.groupHaar (complexGeneralLinearHaar (k + 1))
  have hμ' : D'.groupHaar = c' • complexGeneralLinearHaar (k + 1) :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hc' : 0 < c' := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  obtain ⟨cB, hcB, hB⟩ := ComplexJacquet.complexLocalUnipotentBlockMeasure (k + 1) 1
    D'.unipotentHaar D.unipotentHaar D'.unipotentHaar_isHaar D.unipotentHaar_isHaar
  let cN : ℝ≥0 := cB * (2 : ℝ≥0) ^ (k + 1)
  have hcN : cN ≠ 0 := mul_ne_zero hcB.ne' (pow_ne_zero _ two_ne_zero)
  have hN : D.unipotentHaar = cN • (D'.unipotentHaar.prod (volume : Measure (Fin (k + 1) → ℂ))).map
      (ComplexJacquet.complexUnipotentBlockJoin (k + 1)) := by
    rw [hB, pi_selfDual_one, Measure.prod_smul_right, Measure.map_smul, smul_smul]
    exact (ComplexJacquet.complexUnipotentBlockJoin (k + 1)).measurable.aemeasurable
  refine ⟨c₀, ((c' * cN : ℝ≥0) : ℝ)⁻¹, by exact_mod_cast hc₀,
    inv_pos.mpr (by exact_mod_cast mul_pos hc' (pos_iff_ne_zero.mpr hcN)),
    fun F hFc hF hFi => ⟨fiber k F ρ, ?_, ?_, ?_⟩⟩
  · exact (integral_lastRow_eq D hμ hρ hFc hF hFi (Θ := fun _ => 1) measurable_const
      (fun _ => by simp)).1
  · intro Θ hΘ hΘb
    exact (integral_lastRow_eq D hμ hρ hFc hF hFi hΘ hΘb).2
  · intro g hg
    have hρg : IsNormalizingFunction (Langlands.GeneralLinear.upperUnipotent (k + 1 + 1) ℂ)
        D.unipotentHaar (fun x => (ρ (x * g) : ℝ≥0∞)) := by
      refine ⟨measurable_coe_nnreal_ennreal.comp
        (hρc.measurable.comp (measurable_id.mul_const g)), fun x => ?_⟩
      simpa only [mul_assoc] using hρ.lintegral_eq_one (x * g)
    have hb := fiber_lastBasis D D' hμ' hcN hN (ρ := fun x => ρ (x * g)) (F := fun x => F (x * g))
      (hρc.measurable.comp (measurable_id.mul_const g)) hρg
      (hFc.comp (continuous_id.mul continuous_const))
      (fun u x => by
        show F (u.val * x * g) = F (x * g)
        rw [mul_assoc, hF]) hg
    rw [fiber_lastRow, hb, smul_smul]

end Main

end Langlands.Global.RankinSelbergGlobal.ComplexLastRowFiber
