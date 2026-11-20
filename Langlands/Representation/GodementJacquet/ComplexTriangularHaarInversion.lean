import Langlands.Global.RankinSelberg.UnfoldingSteps
import Langlands.Representation.GodementJacquet.ComplexTriangularHaar

/-! # Inversion in the triangular Haar coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal.Unfolding (isInvInvariant_of_isMulRightInvariant)

variable (n : ℕ)
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "M" => Matrix I I ℂ
local notation "G" => GeneralLinear n ℂ
local notation "U" => upperUnipotent n ℂ
local notation "D" => I → ℂˣ

local instance triangularInversionMatrixSecondCountable : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (I → I → ℂ))
local instance triangularInversionGLSecondCountable : SecondCountableTopology G :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).isInducing.secondCountableTopology
local instance triangularInversionGLMeasurable : MeasurableSpace G := borel _
local instance triangularInversionGLBorel : BorelSpace G := ⟨rfl⟩
local instance triangularInversionUnitsMeasurable : MeasurableSpace ℂˣ := borel _
local instance triangularInversionUnitsBorel : BorelSpace ℂˣ := ⟨rfl⟩
local instance triangularInversionUnitsSecondCountable : SecondCountableTopology ℂˣ :=
  (show IsEmbedding (Units.val : ℂˣ → ℂ) from Units.isEmbedding_val₀).isInducing.secondCountableTopology

private theorem upperEntryRightCorrection_depends (a : U) (ij : J) (X Y : J → ℂ)
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

private theorem upperEntry_rightTranslation_preserving (ν : AdditiveHaarMeasure ℂ)
    [SigmaFinite ν.measure] (a : U) :
    MeasurePreserving
      (fun X => upperEntryCoordinates n ((upperEntryCoordinates n).symm X * a))
      (upperEntryProductMeasure ν n) (upperEntryProductMeasure ν n) := by
  let e := upperEntryCoordinates n (K := ℂ)
  let f (X : J → ℂ) := e (e.symm X * a) - X
  have hf : Continuous f :=
    (e.continuous.comp (e.symm.continuous.mul continuous_const)).sub continuous_id
  have h := finiteTriangularTranslation J (fun _ => ℂ) (fun _ => ν.measure)
    (fun ij => ij.1.2.val - ij.1.1.val) f hf.measurable (upperEntryRightCorrection_depends n a)
  have hfun : (fun X ij => f X ij + X ij) = fun X => e (e.symm X * a) := by
    funext X ij
    exact sub_add_cancel _ _
  rw [hfun] at h
  exact h

/-- The product of additive Haar measures in the strict upper entries
is also right invariant on the unipotent group. -/
theorem upperEntryProductMeasure_isMulRightInvariant (ν : AdditiveHaarMeasure ℂ)
    [SigmaFinite ν.measure] :
    IsMulRightInvariant
      ((upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm) := by
  let e := upperEntryCoordinates n (K := ℂ)
  constructor
  intro a
  have hm : Measurable (fun u : U => u * a) := (continuous_id.mul continuous_const).measurable
  rw [Measure.map_map hm e.symm.measurable]
  have hfun : (fun u : U => u * a) ∘ e.symm = e.symm ∘ (fun X => e (e.symm X * a)) := by
    funext X
    simp
  have h := upperEntry_rightTranslation_preserving n ν a
  rw [hfun, ← Measure.map_map e.symm.measurable h.measurable, h.map_eq]

/-- Inversion of an upper-unipotent factor preserves the entry Haar measure. -/
theorem upperEntryProductMeasure_measurePreserving_inv (ν : AdditiveHaarMeasure ℂ)
    [SigmaFinite ν.measure] :
    let μ := (upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm
    MeasurePreserving (Inv.inv : U → U) μ μ := by
  let μ := (upperEntryProductMeasure ν n).map (upperEntryCoordinates n (K := ℂ)).symm
  let e := upperEntryCoordinates n (K := ℂ)
  let : LocallyCompactSpace U := e.isClosedEmbedding.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace U := e.isInducing.pseudoMetrizableSpace
  let : SecondCountableTopology U := e.secondCountableTopology
  let : μ.IsHaarMeasure := upperEntryProductMeasure_isHaar ν
  let : μ.IsMulRightInvariant := upperEntryProductMeasure_isMulRightInvariant n ν
  let : μ.IsInvInvariant := isInvInvariant_of_isMulRightInvariant μ
  exact Measure.measurePreserving_inv μ

/-- Every Haar measure on the diagonal group is preserved by inversion. -/
theorem complexDiagonal_measurePreserving_inv (μ : Measure D) [μ.IsHaarMeasure] :
    MeasurePreserving (Inv.inv : D → D) μ μ := by
  let : LocallyCompactSpace ℂˣ := (show IsOpenEmbedding (Units.val : ℂˣ → ℂ) from
    IsOpenUnits.isOpenEmbedding_unitsVal).locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace ℂˣ :=
    Units.isEmbedding_val₀.isInducing.pseudoMetrizableSpace
  let : μ.IsMulRightInvariant := inferInstance
  let : μ.IsInvInvariant := isInvInvariant_of_isMulRightInvariant μ
  exact Measure.measurePreserving_inv μ

/-- The involutive inverse transpose automorphism preserves matrix Haar measure. -/
theorem complexMatrixHaar_measurePreserving_inverseTranspose
    (μ : Measure M) [μ.IsAddHaarMeasure] :
    MeasurePreserving (inverseTranspose n ℂ) (complexMatrixHaar n μ) (complexMatrixHaar n μ) := by
  let : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (I → I → ℂ))
  let : LocallyCompactSpace G :=
    (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
  let μG := complexMatrixHaar n μ
  let : μG.IsHaarMeasure := complexMatrixHaar_isHaar n μ
  let e := inverseTransposeContinuous n ℂ
  refine ⟨e.continuous.measurable, ?_⟩
  have htrans : e.trans e = ContinuousMulEquiv.refl G := by
    apply ContinuousMulEquiv.ext
    intro g
    exact inverseTranspose_involutive n ℂ g
  have hc : mulEquivHaarChar e ^ 2 = 1 ^ 2 := by
    rw [pow_two, ← mulEquivHaarChar_trans, htrans, mulEquivHaarChar_refl, one_pow]
  have h₁ : mulEquivHaarChar e = 1 := (pow_left_injective (by decide : 2 ≠ 0)) hc
  change μG.map e = μG
  simpa only [h₁, one_smul] using mulEquivHaarChar_smul_map μG e

end Langlands.GodementJacquet
