import Langlands.Analysis.Local.InvolutiveHaarCharacter
import Langlands.Global.RankinSelberg.RealTriangularHaar
import Langlands.Global.RankinSelberg.UnfoldingSteps
import Langlands.Group.GL.Maps
import Langlands.Representation.Archimedean.PrincipalSeriesGramFormula

/-! # Inversion in the real diagonal and upper-unipotent coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal.Unfolding (isInvInvariant_of_isMulRightInvariant)

variable (n : ℕ)
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "M" => Matrix I I ℝ
local notation "G" => GeneralLinear n ℝ
local notation "U" => upperUnipotent n ℝ
local notation "D" => I → ℝˣ
local notation "Kc" => unitaryCompact ℝ n
local notation "ι" => inverseTranspose n ℝ

local instance realInvMatrixSecondCountable : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (I → I → ℝ))
local instance realInvGLSecondCountable : SecondCountableTopology G :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology
local instance realInvGLMeasurable : MeasurableSpace G := borel _
local instance realInvGLBorel : BorelSpace G := ⟨rfl⟩
local instance realInvUnitsMeasurable : MeasurableSpace ℝˣ := borel _
local instance realInvUnitsBorel : BorelSpace ℝˣ := ⟨rfl⟩
local instance realInvUnitsSecondCountable : SecondCountableTopology ℝˣ :=
  Units.isEmbedding_val₀.isInducing.secondCountableTopology

private theorem upperEntryRightCorrection_depends (a : U) (ij : J) (X Y : J → ℝ)
    (h : ∀ kl : J, kl.1.2.val - kl.1.1.val < ij.1.2.val - ij.1.1.val → X kl = Y kl) :
    (upperEntryCoordinates n ((upperEntryCoordinates n).symm X * a) - X) ij =
      (upperEntryCoordinates n ((upperEntryCoordinates n).symm Y * a) - Y) ij := by
  simp only [Pi.sub_apply, upperEntryCoordinates_mul, Homeomorph.apply_symm_apply]
  have hs :
      (∑ k : {k : I // ij.1.1 < k ∧ k < ij.1.2},
        X ⟨(ij.1.1, k), k.2.1⟩ * upperEntryCoordinates n a ⟨(k, ij.1.2), k.2.2⟩) =
      ∑ k : {k : I // ij.1.1 < k ∧ k < ij.1.2},
        Y ⟨(ij.1.1, k), k.2.1⟩ * upperEntryCoordinates n a ⟨(k, ij.1.2), k.2.2⟩ := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h ⟨(ij.1.1, k), k.2.1⟩]
    have hi : ij.1.1.val < k.val.val := k.2.1
    have hj : k.val.val < ij.1.2.val := k.2.2
    dsimp
    omega
  rw [hs]
  abel

private theorem upperEntry_rightTranslation_preserving (ν : AdditiveHaarMeasure ℝ)
    [SigmaFinite ν.measure] (a : U) :
    MeasurePreserving
      (fun X => upperEntryCoordinates n ((upperEntryCoordinates n).symm X * a))
      (upperEntryProductMeasure ν n) (upperEntryProductMeasure ν n) := by
  let e := upperEntryCoordinates n (K := ℝ)
  let f (X : J → ℝ) := e (e.symm X * a) - X
  have hf : Continuous f :=
    (e.continuous.comp (e.symm.continuous.mul continuous_const)).sub continuous_id
  have h := finiteTriangularTranslation J (fun _ => ℝ) (fun _ => ν.measure)
    (fun ij => ij.1.2.val - ij.1.1.val) f hf.measurable (upperEntryRightCorrection_depends n a)
  have hfun : (fun X ij => f X ij + X ij) = fun X => e (e.symm X * a) := by
    funext X ij
    exact sub_add_cancel _ _
  rw [hfun] at h
  exact h

private theorem upperEntryProductMeasure_isMulRightInvariant (ν : AdditiveHaarMeasure ℝ)
    [SigmaFinite ν.measure] :
    IsMulRightInvariant
      ((upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℝ)).symm) := by
  let e := upperEntryCoordinates n (K := ℝ)
  constructor
  intro a
  have hm : Measurable (fun u : U => u * a) := (continuous_id.mul continuous_const).measurable
  rw [Measure.map_map hm e.symm.measurable]
  have hfun : (fun u : U => u * a) ∘ e.symm = e.symm ∘ (fun X => e (e.symm X * a)) := by
    funext X
    simp
  have h := upperEntry_rightTranslation_preserving n ν a
  rw [hfun, ← Measure.map_map e.symm.measurable h.measurable, h.map_eq]

/-- Inversion preserves the pushed-forward upper-entry Haar measure. -/
theorem realUpperEntryProductMeasure_measurePreserving_inv (ν : AdditiveHaarMeasure ℝ)
    [SigmaFinite ν.measure] :
    let μ := (upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℝ)).symm
    MeasurePreserving (Inv.inv : U → U) μ μ := by
  let μ := (upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℝ)).symm
  let e := upperEntryCoordinates n (K := ℝ)
  let : LocallyCompactSpace U := e.isClosedEmbedding.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace U := e.isInducing.pseudoMetrizableSpace
  let : SecondCountableTopology U := e.secondCountableTopology
  let : μ.IsHaarMeasure := upperEntryProductMeasure_isHaar ν
  let : μ.IsMulRightInvariant := upperEntryProductMeasure_isMulRightInvariant n ν
  let : μ.IsInvInvariant := isInvInvariant_of_isMulRightInvariant μ
  exact Measure.measurePreserving_inv μ

/-- Inversion preserves the full product multiplicative measure. -/
theorem realDiagonalHaar_measurePreserving_inv :
    MeasurePreserving (Inv.inv : D → D) (realDiagonalHaar n) (realDiagonalHaar n) := by
  let : LocallyCompactSpace ℝˣ := IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace ℝˣ := Units.isEmbedding_val₀.isInducing.pseudoMetrizableSpace
  let μ := realDiagonalHaar n
  let : μ.IsHaarMeasure := inferInstanceAs (Measure.pi fun _ : I =>
    Langlands.Global.RankinSelbergGlobal.RealRankZero.unitsHaar).IsHaarMeasure
  let : μ.IsMulRightInvariant := inferInstance
  let : μ.IsInvInvariant := isInvInvariant_of_isMulRightInvariant μ
  exact Measure.measurePreserving_inv μ

/-- The inverse transpose automorphism preserves any real general-linear Haar measure. -/
theorem realHaar_measurePreserving_inverseTranspose (μ : Measure G) [μ.IsHaarMeasure] :
    MeasurePreserving ι μ μ := by
  let : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (I → I → ℝ))
  let : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace
  let e := inverseTransposeContinuous n ℝ
  refine ⟨e.continuous.measurable, ?_⟩
  have he := RankinSelberg.TwoBlockFirstBlockLaurent.mulEquivHaarChar_eq_one_of_involutive e
    (inverseTranspose_involutive n ℝ)
  change μ.map e = μ
  simpa only [he, one_smul] using mulEquivHaarChar_smul_map μ e

/-- Inverse transpose fixes the real orthogonal subgroup pointwise. -/
theorem realInverseTranspose_unitary_eq (k : Kc) : ι k.val = k.val := by
  apply Units.ext
  rw [inverseTranspose_coe]
  rw [Units.inv_eq_of_mul_eq_one_right (GramFormula.mul_transpose_eq_one_of_mem k.property),
    Matrix.transpose_transpose]

/-- Actual matrix of the dual triangular point after diagonal and unipotent inversion. -/
theorem realInverseTranspose_triangularPoint (d : D) (u : U) (k : Kc) :
    (ι (diagonalMatrixUnits ℝ d⁻¹ * (u⁻¹).val * k.val)).val =
      (u.val.val * (diagonalMatrixUnits ℝ d).val).transpose * k.val.val := by
  have hd : ι (diagonalMatrixUnits ℝ d⁻¹) = diagonalMatrixUnits ℝ d := by
    apply Units.ext
    rw [inverseTranspose_coe, ← map_inv, inv_inv, diagonalMatrixUnits_val, Matrix.diagonal_transpose]
  rw [map_mul, map_mul, hd, realInverseTranspose_unitary_eq, Units.val_mul, Units.val_mul,
    Matrix.transpose_mul, inverseTranspose_coe, Subgroup.coe_inv, inv_inv,
    diagonalMatrixUnits_val, Matrix.diagonal_transpose]

end Langlands.GodementJacquet
