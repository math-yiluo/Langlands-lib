import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAveraging
import Langlands.Group.GL.UpperBruhatCells

/-!
# Pointwise compact averaging on a rank-one matrix box

A sufficiently deep box identifies a model function with its value at the
rank-one diagonal of the determinant. A compact left averaging subgroup can
therefore be chosen to preserve the function pointwise on that box.
-/

noncomputable section

namespace Langlands.RankinSelberg.RankOneBox

open MeasureTheory Topology GeneralLinear HarmonicAnalysis Whittaker Conductor RankOneIwasawa
open UnequalRankMirabolicUnitTest
open scoped NNReal ENNReal

universe uF uV

section Algebra

variable {E : Type*} [Field E]

/-- The diagonal with the determinant in the first coordinate and ones elsewhere. -/
def determinantRankOne (n : ℕ) : Langlands.GeneralLinear (n + 1) E →*
    Langlands.GeneralLinear (n + 1) E where
  toFun g := Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det g) 1)
  map_one' := by
    have hc : Fin.cons (1 : Eˣ) (1 : Fin n → Eˣ) = (1 : Fin (n + 1) → Eˣ) := by
      funext i
      induction i using Fin.cases <;> simp
    rw [map_one, hc, map_one]
  map_mul' g h := by
    have hc : Fin.cons (Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det h)
        (1 : Fin n → Eˣ) =
        (Fin.cons (Matrix.GeneralLinearGroup.det g) 1 : Fin (n + 1) → Eˣ) *
          (Fin.cons (Matrix.GeneralLinearGroup.det h) 1 : Fin (n + 1) → Eˣ) := by
      funext i
      induction i using Fin.cases <;> simp
    rw [map_mul, hc, map_mul]

@[simp]
theorem determinantRankOne_point {p : ℕ} [Fact p.Prime] (F : PadicField p)
    {n : ℕ} (x : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin n → F.Carrierˣ)) ×
      upperUnipotent (n + 1) F.Carrier) :
    determinantRankOne n (point x) =
      Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det x.1.1) 1) := by
  change Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det (point x)) 1) = _
  rw [det_point F]

variable [TopologicalSpace E] [IsTopologicalRing E]

/-- The determinant-rank-one endomorphism is continuous. -/
theorem continuous_determinantRankOne (n : ℕ) :
    Continuous (determinantRankOne (E := E) n) := by
  apply (continuous_diagonalUnits (n + 1)).comp
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero => exact Matrix.GeneralLinearGroup.continuous_det
  | succ i => exact continuous_const

end Algebra

section Pointwise

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance boxCoefficientTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance boxCoefficientValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance boxCoefficientLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance boxCoefficientT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance boxCoefficientMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance boxCoefficientBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)

/-- On a deep box, a model function only depends on the determinant-rank-one diagonal. -/
theorem modelFunction_eq_determinantRankOne_of_mem_box {A q : ℤ} {a : ℕ}
    (ha : 0 < a) (hA : 0 ≤ A) (hq : q ≤ 0)
    (hL : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (q - A))
    (hψ : ∀ z ∈ 𝓛 q, ψ z = 1)
    (hlev : ∀ z ∈ levelSet F.Carrier a, z ∈ 𝓛 q)
    (hstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g)
    (hDstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * determinantRankOne (m + 1) y) =
        glModelFunction ψ (m + 1) σ ℓ w g)
    {g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier}
    (hg : g.val ∈ box F A q a) :
    glModelFunction ψ (m + 1) σ ℓ w g =
      glModelFunction ψ (m + 1) σ ℓ w (determinantRankOne (m + 1) g) := by
  obtain ⟨y, hy, hb⟩ := exists_mem_principalLevel_mul_inv_upper F ha hg
  obtain ⟨⟨⟨g₁, t⟩, u⟩, hx⟩ := exists_point_eq (g * y⁻¹) hb
  have hbox : (point ((g₁, t), u)).val ∈ box F A q a := by
    rw [hx, Units.val_mul]
    exact (mul_mem_box_iff F hA hq hL g.val (inv_mem hy)).2 hg
  have ht := torusFactor_mem F ha (mem_torusBox_of_mem_box F hbox)
  have hu : u ∈ unipotentBox F q a := by
    have h := hbox
    rw [point_eq_mul F, Units.val_mul,
      mul_mem_box_iff F hA hq hL _ ht, mem_box_unipotent_mul_iff] at h
    exact h.2
  have hW : glModelFunction ψ (m + 1) σ ℓ w (point ((g₁, t), u)) =
      glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g₁) := by
    rw [point_eq_mul F, hstab _ ht, glModelFunction_equivariance,
      standardCharacter_eq_one F ψ hψ hlev hu, one_mul]
    rfl
  calc
    glModelFunction ψ (m + 1) σ ℓ w g =
        glModelFunction ψ (m + 1) σ ℓ w (g * y⁻¹) := (hstab _ (inv_mem hy) g).symm
    _ = glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g₁) := by rw [← hx]; exact hW
    _ = glModelFunction ψ (m + 1) σ ℓ w
        (determinantRankOne (m + 1) (g * y⁻¹)) := by
      rw [← hx, determinantRankOne_point F]
      rfl
    _ = glModelFunction ψ (m + 1) σ ℓ w (determinantRankOne (m + 1) g) := by
      rw [map_mul, hDstab _ (inv_mem hy)]

/-- Normalized averaging is pointwise the original function wherever every
left translate in the subgroup has the same value. -/
theorem averagedModelCoefficient_eq_of_left_invariant (hσ : IsSmooth σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)))
    (g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier)
    (hinv : ∀ k ∈ K, glModelFunction ψ (m + 1) σ ℓ w (k * g) =
      glModelFunction ψ (m + 1) σ ℓ w g) :
    (GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w).val g =
      glModelFunction ψ (m + 1) σ ℓ w g := by
  have hmass : ((generalLinearHaar F.Carrier (m + 1)).real (K : Set _) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨(K.isOpen.measure_pos _ ⟨1, K.one_mem⟩).ne', hK.measure_lt_top.ne⟩
  rw [GodementJacquet.Padic.averagedModelCoefficient_apply, GodementJacquet.normalizedLeftAverage]
  have heq : (∫ k in (K : Set _), glModelFunction ψ (m + 1) σ ℓ w (k * g)
      ∂generalLinearHaar F.Carrier (m + 1)) =
      ∫ _ in (K : Set _), glModelFunction ψ (m + 1) σ ℓ w g
        ∂generalLinearHaar F.Carrier (m + 1) := by
    apply setIntegral_congr_fun K.isOpen.measurableSet
    exact hinv
  rw [heq, setIntegral_const, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ hmass, one_mul]

end Pointwise

end Langlands.RankinSelberg.RankOneBox
