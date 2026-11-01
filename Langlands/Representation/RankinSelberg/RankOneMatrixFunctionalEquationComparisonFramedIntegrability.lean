import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonProductIntegrability
import Mathlib.LinearAlgebra.Matrix.RowCol

/-! Compact support on unipotent times full matrices from an invertible frame. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.CompactWhittakerSynthesis

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis GeneralLinear Topology

universe uK uF

section General

variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K]

/-- An equivariant frame, invertible on the second test's support, bounds the
joint support even when the first test meets singular matrices. -/
theorem hasCompactSupport_framed_matrix_product (r : ℕ)
    (H : Subgroup (Langlands.GeneralLinear r K))
    (hH : IsClosed (H : Set (Langlands.GeneralLinear r K)))
    (hdet : ∀ u : H, u.val.val.det = 1)
    (frame : Matrix (Fin r) (Fin r) K → Matrix (Fin r) (Fin r) K)
    (hframe : Continuous frame)
    (heq : ∀ (u : H) A, frame (u.val.val * A) = u.val.val * frame A)
    (Φ₁ Φ₂ : SchwartzBruhat (Matrix (Fin r) (Fin r) K))
    (hΦ₂ : ∀ A ∈ tsupport (Φ₂ : _ → ℂ), frame A ∈
      Set.range (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K)) :
    HasCompactSupport (fun z : H × Matrix (Fin r) (Fin r) K =>
      Φ₁ (z.1.val.val * z.2) * Φ₂ z.2) := by
  let T₂ := frame '' tsupport (Φ₂ : _ → ℂ)
  have hT₂ : IsCompact T₂ := Φ₂.hasCompactSupport.image hframe
  have hrange : T₂ ⊆ Set.range
      (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K) := by
    rintro _ ⟨A, hA, rfl⟩
    exact hΦ₂ A hA
  let G₂ := (Units.val : Langlands.GeneralLinear r K →
    Matrix (Fin r) (Fin r) K) ⁻¹' T₂
  have hG₂ : IsCompact G₂ :=
    (isEmbedding_generalLinear_val r).isInducing.isCompact_preimage' hT₂ hrange
  let T₁ := frame '' tsupport (Φ₁ : _ → ℂ)
  let G₁ := {g : Langlands.GeneralLinear r K | g.val ∈ T₁ ∧
    g.val.det ∈ (fun a : Langlands.GeneralLinear r K => a.val.det) '' G₂}
  have hG₁ : IsCompact G₁ := isCompact_matrixDetRestriction r G₂ hG₂ T₁
    (Φ₁.hasCompactSupport.image hframe)
  let U := (fun z : Langlands.GeneralLinear r K × Langlands.GeneralLinear r K =>
    z.1 * z.2⁻¹) '' (G₁ ×ˢ G₂)
  have hU : IsCompact U := (hG₁.prod hG₂).image
    (continuous_fst.mul continuous_snd.inv)
  have hUH : IsCompact ((Subtype.val : H → Langlands.GeneralLinear r K) ⁻¹' U) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hU
  apply HasCompactSupport.intro (hUH.prod Φ₂.hasCompactSupport)
  intro z hz
  by_contra hne
  have h₁ := subset_tsupport (Φ₁ : _ → ℂ) (mul_ne_zero_iff.mp hne).1
  have h₂ := subset_tsupport (Φ₂ : _ → ℂ) (mul_ne_zero_iff.mp hne).2
  obtain ⟨g₂, hg₂⟩ := hΦ₂ z.2 h₂
  have hg₂mem : g₂ ∈ G₂ := by
    change g₂.val ∈ T₂
    exact ⟨z.2, h₂, hg₂.symm⟩
  have hg₁val : (z.1.val * g₂).val = frame (z.1.val.val * z.2) := by
    rw [Units.val_mul, hg₂, heq]
  have hg₁mem : z.1.val * g₂ ∈ G₁ := by
    refine ⟨?_, g₂, hg₂mem, ?_⟩
    · rw [hg₁val]
      exact ⟨z.1.val.val * z.2, h₁, rfl⟩
    · change g₂.val.det = (z.1.val * g₂).val.det
      rw [Units.val_mul, Matrix.det_mul, hdet z.1, one_mul]
  apply hz
  refine ⟨?_, h₂⟩
  change z.1.val ∈ U
  exact ⟨(z.1.val * g₂, g₂), ⟨hg₁mem, hg₂mem⟩, by simp⟩

/-- Continuous weights preserve integrability of the framed product for any
supplied measures finite on compact sets. -/
theorem integrable_weighted_framed_matrix_product (r : ℕ)
    (H : Subgroup (Langlands.GeneralLinear r K))
    (hH : IsClosed (H : Set (Langlands.GeneralLinear r K)))
    (hdet : ∀ u : H, u.val.val.det = 1)
    (frame : Matrix (Fin r) (Fin r) K → Matrix (Fin r) (Fin r) K)
    (hframe : Continuous frame)
    (heq : ∀ (u : H) A, frame (u.val.val * A) = u.val.val * frame A)
    [SecondCountableTopology (Langlands.GeneralLinear r K)]
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (Matrix (Fin r) (Fin r) K)]
    [BorelSpace (Matrix (Fin r) (Fin r) K)]
    (μH : Measure H) (μM : Measure (Matrix (Fin r) (Fin r) K))
    [SFinite μM] [IsFiniteMeasureOnCompacts μH] [IsFiniteMeasureOnCompacts μM]
    (Φ₁ Φ₂ : SchwartzBruhat (Matrix (Fin r) (Fin r) K))
    (hΦ₂ : ∀ A ∈ tsupport (Φ₂ : _ → ℂ), frame A ∈
      Set.range (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K))
    (a : H → ℂ) (b : Matrix (Fin r) (Fin r) K → ℂ)
    (ha : Continuous a) (hb : Continuous b) :
    Integrable (fun z : H × Matrix (Fin r) (Fin r) K =>
      a z.1 * Φ₁ (z.1.val.val * z.2) * Φ₂ z.2 * b z.2) (μH.prod μM) := by
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hc : HasCompactSupport (fun z : H × Matrix (Fin r) (Fin r) K =>
      a z.1 * (Φ₁ (z.1.val.val * z.2) * Φ₂ z.2) * b z.2) :=
    (hasCompactSupport_framed_matrix_product r H hH hdet frame hframe heq Φ₁ Φ₂ hΦ₂
      ).mul_left.mul_right
  have hcont : Continuous (fun z : H × Matrix (Fin r) (Fin r) K =>
      a z.1 * (Φ₁ (z.1.val.val * z.2) * Φ₂ z.2) * b z.2) :=
    ((ha.comp continuous_fst).mul
      ((Φ₁.continuous.comp
        (((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
          ).mul continuous_snd)).mul (Φ₂.continuous.comp continuous_snd))).mul
      (hb.comp continuous_snd)
  simpa only [mul_assoc] using hcont.integrable_of_hasCompactSupport hc

end General

section FirstColumn

variable {K : Type uK} [Field K]

/-- Replace the first column by the first column of the identity. -/
def firstColumnFrame (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  A.updateCol 0 (fun i => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i 0)

theorem firstColumnFrame_mul (n : ℕ) (u : upperUnipotent (n + 1) K)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    firstColumnFrame n (u.val.val * A) = u.val.val * firstColumnFrame n A := by
  have he : Matrix.mulVec u.val.val
      (fun i => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i 0) =
      (fun i => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i 0) := by
    funext i
    change (u.val.val * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) i 0 = _
    rw [Matrix.mul_one]
    by_cases hi : i = 0
    · subst i
      simp
    · rw [UpperUnipotent.entry_eq_zero u (Fin.pos_iff_ne_zero.mpr hi),
        Matrix.one_apply_ne hi]
  rw [firstColumnFrame, firstColumnFrame, Matrix.mul_updateCol, he]

theorem continuous_firstColumnFrame [TopologicalSpace K] (n : ℕ) :
    Continuous (firstColumnFrame (K := K) n) :=
  continuous_id.matrix_updateCol 0 continuous_const

theorem det_firstColumnFrame (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (firstColumnFrame n A).det = (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [firstColumnFrame, Matrix.one_apply]
  congr 1

end FirstColumn

section CanonicalPadic

open Whittaker Conductor UnequalRankMirabolicUnitTest

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

/-- The first-column frame of every matrix in the actual comparison box is
invertible; the original matrix itself may be singular. -/
theorem firstColumnFrame_mem_range_of_mem_box (n : ℕ) (A q : ℤ) {a : ℕ}
    (ha : 0 < a)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)
    (hX : X ∈ RankOneBox.box F A q a) :
    firstColumnFrame n X ∈ Set.range
      (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) := by
  let Y := (firstColumnFrame n X).updateRow 0
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) 0)
  have hY : ∀ i j, Y i j -
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈
      levelSet F.Carrier a := by
    intro i j
    by_cases hi : i = 0
    · subst i
      simp only [Y, Matrix.updateRow_self, sub_self]
      exact zero_mem_levelSet a
    · by_cases hj : j = 0
      · subst j
        simp only [Y, Matrix.updateRow_ne hi, firstColumnFrame, Matrix.updateCol_self,
          sub_self]
        exact zero_mem_levelSet a
      · simp only [Y, Matrix.updateRow_ne hi, firstColumnFrame, Matrix.updateCol_ne hj]
        exact ((RankOneBox.mem_box_iff F X).mp hX).2.2 i hi j
  obtain ⟨y, _, hy⟩ := exists_mem_principalLevelSubgroup ha Y hY
  have hdet : (firstColumnFrame n X).det = y.val.det := by
    rw [hy, det_firstColumnFrame, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [Y, firstColumnFrame, Matrix.updateRow_apply, Matrix.one_apply]
    congr 1
  exact ⟨((Matrix.isUnit_iff_isUnit_det (firstColumnFrame n X)).mpr
    (Ne.isUnit (hdet ▸ y.det_ne_zero))).unit, rfl⟩

/-- Canonical unipotent Haar and the actual inverse standard character, with an
arbitrary supplied compact-finite full-matrix measure and continuous weight. -/
theorem integrable_unipotent_framed_matrix_product
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (μM : Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    [SFinite μM] [IsFiniteMeasureOnCompacts μM]
    (Φ₁ Φ₂ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ₂ : ∀ X ∈ tsupport (Φ₂ : _ → ℂ), firstColumnFrame n X ∈
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) (hb : Continuous b) :
    Integrable (fun z : upperUnipotent (n + 1) F.Carrier ×
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier =>
      (((standardCharacter ψ n z.1)⁻¹ : ℂˣ) : ℂ) *
        Φ₁ (z.1.val.val * z.2) * Φ₂ z.2 * b z.2)
      ((unipotentHaar F.Carrier n).prod μM) := by
  exact integrable_weighted_framed_matrix_product (n + 1)
    (upperUnipotent (n + 1) F.Carrier) UpperUnipotent.isClosed
    (fun u => unipotent_det u) (firstColumnFrame n) (continuous_firstColumnFrame n)
    (firstColumnFrame_mul n) (unipotentHaar F.Carrier n) μM Φ₁ Φ₂ hΦ₂
    (fun u => (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ)) b
    (Units.continuous_val.comp (continuous_inv.comp
      (standardCharacterContinuous ψ n).continuous)) hb

/-- A second test supported in the actual positive-level box satisfies the
frame condition, for every matrix size including size one. -/
theorem integrable_unipotent_box_matrix_product
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (μM : Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    [SFinite μM] [IsFiniteMeasureOnCompacts μM]
    (Φ₁ Φ₂ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΦ₂ : tsupport (Φ₂ : _ → ℂ) ⊆ RankOneBox.box F A q a)
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) (hb : Continuous b) :
    Integrable (fun z : upperUnipotent (n + 1) F.Carrier ×
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier =>
      (((standardCharacter ψ n z.1)⁻¹ : ℂˣ) : ℂ) *
        Φ₁ (z.1.val.val * z.2) * Φ₂ z.2 * b z.2)
      ((unipotentHaar F.Carrier n).prod μM) :=
  integrable_unipotent_framed_matrix_product F ψ n μM Φ₁ Φ₂
    (fun X hX => firstColumnFrame_mem_range_of_mem_box F n A q ha X (hΦ₂ hX)) b hb

/-- Fubini for the actual unipotent Haar and full-matrix measure under the box
support bound, without restricting the first matrix test to the invertible locus. -/
theorem integral_unipotent_box_matrix_swap
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (μM : Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    [SFinite μM] [IsFiniteMeasureOnCompacts μM]
    (Φ₁ Φ₂ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΦ₂ : tsupport (Φ₂ : _ → ℂ) ⊆ RankOneBox.box F A q a)
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) (hb : Continuous b) :
    (∫ u : upperUnipotent (n + 1) F.Carrier,
      ∫ X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier,
        (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) *
          Φ₁ (u.val.val * X) * Φ₂ X * b X ∂μM ∂unipotentHaar F.Carrier n) =
    ∫ X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier,
      ∫ u : upperUnipotent (n + 1) F.Carrier,
        (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) *
          Φ₁ (u.val.val * X) * Φ₂ X * b X ∂unipotentHaar F.Carrier n ∂μM :=
  integral_integral_swap
    (integrable_unipotent_box_matrix_product F ψ n μM Φ₁ Φ₂ A q ha hΦ₂ b hb)

/-- The same genuine bound for the supplied additive product measure used by
the full plus-sign rectangular Fourier integral. -/
theorem integrable_unipotent_box_rectangular_product
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ₁ Φ₂ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΦ₂ : tsupport (Φ₂ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    Integrable (fun z : upperUnipotent (n + 1) F.Carrier ×
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier =>
      (((standardCharacter ψ n z.1)⁻¹ : ℂˣ) : ℂ) *
        Φ₁ (z.1.val.val * z.2) * Φ₂ z.2)
      ((unipotentHaar F.Carrier n).prod (rectangularMeasure ν (n + 1) (n + 1))) := by
  simpa only [mul_one] using integrable_unipotent_box_matrix_product F ψ n
    (rectangularMeasure ν (n + 1) (n + 1)) Φ₁ Φ₂ A q ha hΦ₂ (fun _ => 1) continuous_const

/-- The actual supplied rectangular additive measure admits the same exchange. -/
theorem integral_unipotent_box_rectangular_swap
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ₁ Φ₂ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΦ₂ : tsupport (Φ₂ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    (∫ u : upperUnipotent (n + 1) F.Carrier,
      ∫ X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier,
        (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) *
          Φ₁ (u.val.val * X) * Φ₂ X
        ∂rectangularMeasure ν (n + 1) (n + 1) ∂unipotentHaar F.Carrier n) =
    ∫ X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier,
      ∫ u : upperUnipotent (n + 1) F.Carrier,
        (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) *
          Φ₁ (u.val.val * X) * Φ₂ X
        ∂unipotentHaar F.Carrier n ∂rectangularMeasure ν (n + 1) (n + 1) :=
  integral_integral_swap
    (integrable_unipotent_box_rectangular_product F ψ ν n Φ₁ Φ₂ A q ha hΦ₂)

end CanonicalPadic

end Langlands.RankinSelberg.CompactWhittakerSynthesis
