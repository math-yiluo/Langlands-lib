import Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceStatement
import Langlands.Representation.RankinSelberg.EqualRankSliceSupportProof
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof

/-!
# Unconditional convergence of the adjacent-rank tensor integral

The pure-tensor scalar integrand has compact support on the inner general
linear group. The first columns give a compact matrix bound; the last column
and smooth Whittaker simple-root support bound the inverse determinant.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct

universe uF uV

section CanonicalTopology

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

/-- The rectangular kernel is continuous, including its inverse-row column. -/
theorem continuous_adjacentRankKernelMatrix (r : ℕ) :
    Continuous (adjacentRankKernelMatrix :
      GeneralLinear (r + 1) F.Carrier →
        Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [adjacentRankKernelMatrix_last]
    exact (continuous_apply i).comp
      (Matrix.GeneralLinearGroup.continuous_apply
        (fun h : GeneralLinear (r + 1) F.Carrier => h⁻¹) continuous_inv (Fin.last r))
  · simp only [adjacentRankKernelMatrix_castSucc]
    exact (continuous_apply j).comp
      (Matrix.GeneralLinearGroup.continuous_apply
        (fun h : GeneralLinear (r + 1) F.Carrier => h) continuous_id i)

/-- The Schwartz factor bounds the last row of the inverse matrix on its support. -/
theorem exists_adjacentRank_lastColumn_bound (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ h : GeneralLinear (r + 1) F.Carrier,
        Φ (adjacentRankKernelMatrix h) ≠ 0 →
          ∀ j, F.canonicalTopologicalData.normalizedAbs (lastRow h⁻¹ j) ≤ C := by
  have hc : Continuous fun m : Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier =>
      ∑ i, F.canonicalTopologicalData.normalizedAbs (m i (Fin.last (r + 1))) :=
    continuous_finsetSum _ fun i _ =>
      F.canonicalTopologicalData.continuous_normalizedAbs.comp
        ((continuous_apply (Fin.last (r + 1))).comp (continuous_apply i))
  obtain ⟨C, hC⟩ :=
    (SchwartzBruhat.hasCompactSupport Φ).isCompact.exists_bound_of_continuousOn
      hc.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun h hh j => ?_⟩
  have hb := hC _ (subset_tsupport _ hh)
  rw [Real.norm_eq_abs] at hb
  calc
    F.canonicalTopologicalData.normalizedAbs (lastRow h⁻¹ j) =
        F.canonicalTopologicalData.normalizedAbs (adjacentRankKernelMatrix h j (Fin.last (r + 1))) := by
          rw [adjacentRankKernelMatrix_last]
          rfl
    _ ≤ ∑ i, F.canonicalTopologicalData.normalizedAbs (adjacentRankKernelMatrix h i (Fin.last (r + 1))) :=
      Finset.single_le_sum
        (f := fun i : Fin (r + 1) =>
          F.canonicalTopologicalData.normalizedAbs
            (adjacentRankKernelMatrix h i (Fin.last (r + 1))))
        (fun i _ => F.canonicalTopologicalData.normalizedAbs_nonneg _) (Finset.mem_univ j)
    _ ≤ |∑ i, F.canonicalTopologicalData.normalizedAbs (adjacentRankKernelMatrix h i (Fin.last (r + 1)))| :=
      le_abs_self _
    _ ≤ C := hb
    _ ≤ max C 1 := le_max_left _ _

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The product of the kernel Schwartz factor and any smooth Whittaker model
coefficient has compact support on the actual inner general linear group. -/
theorem adjacentRankPure_hasCompactSupport
    (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    HasCompactSupport (fun h : GeneralLinear (r + 1) F.Carrier =>
      Φ (adjacentRankKernelMatrix h) * glModelFunction ψ r σ ℓ W h⁻¹) := by
  obtain ⟨R, hR, hroot⟩ :=
    Whittaker.smoothSimpleRootSupport.{uF,uV} F F.canonicalTopologicalData r ψ V σ hσ ℓ W
  obtain ⟨C, hC, hrow⟩ := exists_adjacentRank_lastColumn_bound F r Φ
  let D : ℝ := ∏ i : Fin (r + 1), R ^ (r - i.val) * C
  have hD : 0 < D :=
    Finset.prod_pos fun i _ => mul_pos (pow_pos hR _) hC
  let S : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) :=
    rectangularFirstColumns '' tsupport (Φ : _ → ℂ) ∩
      {A | D⁻¹ ≤ F.canonicalTopologicalData.normalizedAbs A.det}
  have hS : IsCompact S :=
    ((SchwartzBruhat.hasCompactSupport Φ).isCompact.image
      continuous_rectangularFirstColumns).inter_right
        (isClosed_le continuous_const
          (F.canonicalTopologicalData.continuous_normalizedAbs.comp continuous_id.matrix_det))
  have hSinv : S ⊆ Set.range
      (Units.val : GeneralLinear (r + 1) F.Carrier →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) := by
    intro A hA
    have hdet : A.det ≠ 0 := by
      intro hz
      have h : D⁻¹ ≤ F.canonicalTopologicalData.normalizedAbs A.det := hA.2
      rw [hz, F.canonicalTopologicalData.normalizedAbs_zero] at h
      exact (inv_pos.mpr hD).not_ge h
    exact ⟨((Matrix.isUnit_iff_isUnit_det A).mpr (Ne.isUnit hdet)).unit, rfl⟩
  have hcompact : IsCompact
      ((Units.val : GeneralLinear (r + 1) F.Carrier →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) ⁻¹' S) :=
    (isEmbedding_generalLinear_val (r + 1)).isInducing.isCompact_preimage' hS hSinv
  refine HasCompactSupport.intro hcompact fun h hh => ?_
  by_contra hnonzero
  have hΦ : Φ (adjacentRankKernelMatrix h) ≠ 0 :=
    fun hz => hnonzero (by rw [hz, zero_mul])
  have hW : W.val.val h⁻¹ ≠ 0 :=
    fun hz => hnonzero (by change Φ _ * W.val.val h⁻¹ = 0; rw [hz, mul_zero])
  have hdet := normalizedAbs_determinant_le_of_simpleRoot F.canonicalTopologicalData r ψ W.val hR hC.le hroot
    h⁻¹ hW (hrow h hΦ)
  have habs : F.canonicalTopologicalData.normalizedAbs (GeneralLinear.determinant h⁻¹ : F.Carrier) =
      (F.canonicalTopologicalData.normalizedAbs (GeneralLinear.determinant h : F.Carrier))⁻¹ := by
    change normalizedAbsoluteValue F.canonicalTopologicalData (GeneralLinear.determinant h⁻¹ : F.Carrier) =
      (normalizedAbsoluteValue F.canonicalTopologicalData (GeneralLinear.determinant h : F.Carrier))⁻¹
    simp only [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
  rw [habs] at hdet
  have hlower : D⁻¹ ≤ F.canonicalTopologicalData.normalizedAbs (GeneralLinear.determinant h : F.Carrier) :=
    (inv_le_comm₀ hD (F.canonicalTopologicalData.normalizedAbs_pos (GeneralLinear.determinant h).ne_zero)).mpr hdet
  apply hh
  exact ⟨⟨adjacentRankKernelMatrix h, subset_tsupport _ hΦ,
    rectangularFirstColumns_adjacentRankKernelMatrix h⟩, hlower⟩

/-- The canonical determinant weight is continuous on GL for every complex
exponent, since its base is strictly positive. -/
theorem continuous_adjacentRank_determinantWeight (m : ℕ) (s : ℂ) :
    Continuous fun h : GeneralLinear m F.Carrier =>
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h s := by
  unfold determinantWeight
  have hc : Continuous fun h : GeneralLinear m F.Carrier =>
      ((normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det h.val) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (F.canonicalTopologicalData.continuous_normalizedAbs.comp
        Units.continuous_val.matrix_det)
  refine hc.cpow continuous_const fun h => ?_
  rw [Complex.ofReal_mem_slitPlane]
  exact (normalizedAbsoluteValue F.canonicalTopologicalData).pos h.det_ne_zero

local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

/-- A pure tensor gives an actually integrable formula (8) integrand, for every
ambient element and every continuous quasicharacter. -/
theorem adjacentRankModelConverges_tmul_of_isSmooth
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ ν) (r : ℕ)
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (g : GeneralLinear (r + 2) F.Carrier) :
    Padic.AdjacentRankModelConverges F ψ ν hself σ ℓ χ (Φ ⊗ₜ W) g := by
  let Φ' := rectangularRho0 ψ ν (r + 1) hself g Φ
  change Integrable (fun h : GeneralLinear (r + 1) F.Carrier =>
    Φ' (adjacentRankKernelMatrix h) * glModelFunction ψ r σ ℓ W h⁻¹ *
      (χ (GeneralLinear.determinant h) : ℂ) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h ((r : ℂ) / 2))
    (generalLinearHaar F.Carrier r)
  apply Continuous.integrable_of_hasCompactSupport
  · have hχ : Continuous fun h : GeneralLinear (r + 1) F.Carrier =>
        (χ (GeneralLinear.determinant h) : ℂ) :=
      Units.continuous_val.comp (χ.continuous.comp GeneralLinear.determinantContinuous.continuous)
    exact ((((SchwartzBruhat.continuous Φ').comp (continuous_adjacentRankKernelMatrix F r)).mul
      ((glModelFunction_continuous ψ r σ hσ ℓ W).comp continuous_inv)).mul hχ).mul
        (continuous_adjacentRank_determinantWeight F _ _)
  · exact ((adjacentRankPure_hasCompactSupport F ψ r σ hσ ℓ Φ' W).mul_right).mul_right

end CanonicalTopology

/-- JPSS Section 6.1, formula (8), converges unconditionally for all test tensors
and all data in the published adjacent-rank model statement. -/
theorem adjacentRankModelConvergence :
    AdjacentRankModelConvergenceStatement.{uF,uV} := by
  intro p _ F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel _
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro ψ ν hself r V _ _ σ hσ ℓ χ Ψ g
  let : MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
  have : BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    exact adjacentRankModelConverges_tmul_of_isSmooth F ψ ν hself r σ hσ.1.1 ℓ χ Φ W g
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    exact AdjacentRankModelConverges.add h₁ h₂

end Langlands.RankinSelberg
