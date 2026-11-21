import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Group.GL.UpperUnipotentEntryCoordinates
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Global.RankinSelberg.UnipotentClassProductProof

/-! # Compatible measures on archimedean unipotent quotients -/

noncomputable section
open MeasureTheory MeasureTheory.Measure
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates
  upperEntryCoordinates_mul upperEntryProductMeasure)
open Langlands.HarmonicAnalysis

section RightTranslation

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] (n : ℕ)
  [MeasurableSpace (GeneralLinear.upperUnipotent n K)] [BorelSpace (GeneralLinear.upperUnipotent n K)]

omit [MeasurableSpace (GeneralLinear.upperUnipotent n K)]
  [BorelSpace (GeneralLinear.upperUnipotent n K)] in
private theorem upperEntry_rightTranslation_preserving (a : GeneralLinear.upperUnipotent n K) :
    MeasurePreserving
      (fun X => upperEntryCoordinates n ((upperEntryCoordinates n).symm X * a))
      (upperEntryProductMeasure ν n) (upperEntryProductMeasure ν n) := by
  let e := upperEntryCoordinates n (K := K)
  let f (X : UpperEntryPair n → K) := e (e.symm X * a) - X
  have hf : Continuous f := (e.continuous.comp (e.symm.continuous.mul continuous_const)).sub continuous_id
  have hdep (ij : UpperEntryPair n) (X Y : UpperEntryPair n → K)
      (h : ∀ kl : UpperEntryPair n,
        kl.1.2.val - kl.1.1.val < ij.1.2.val - ij.1.1.val → X kl = Y kl) :
      f X ij = f Y ij := by
    simp only [f, e, Pi.sub_apply, upperEntryCoordinates_mul, Homeomorph.apply_symm_apply]
    have hs :
        (∑ k : {k : Fin n // ij.1.1 < k ∧ k < ij.1.2},
          X ⟨(ij.1.1, k), k.2.1⟩ * e a ⟨(k, ij.1.2), k.2.2⟩) =
        ∑ k : {k : Fin n // ij.1.1 < k ∧ k < ij.1.2},
          Y ⟨(ij.1.1, k), k.2.1⟩ * e a ⟨(k, ij.1.2), k.2.2⟩ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [h ⟨(ij.1.1, k), k.2.1⟩]
      have hi : ij.1.1.val < k.val.val := k.2.1
      have hj : k.val.val < ij.1.2.val := k.2.2
      dsimp
      omega
    rw [show e a = upperEntryCoordinates n a from rfl] at hs
    rw [hs]
    abel
  have hpres := finiteTriangularTranslation (UpperEntryPair n) (fun _ => K)
    (fun _ => ν.measure) (fun ij => ij.1.2.val - ij.1.1.val) f hf.measurable hdep
  have he : (fun X ij => f X ij + X ij) = fun X => e (e.symm X * a) := by
    funext X ij
    exact sub_add_cancel _ _
  rw [he] at hpres
  exact hpres

private theorem upperEntryHaar_isMulRightInvariant :
    ((upperEntryProductMeasure ν n).map (upperEntryCoordinates n).symm).IsMulRightInvariant := by
  let e := upperEntryCoordinates n (K := K)
  refine ⟨fun a => ?_⟩
  have hp := upperEntry_rightTranslation_preserving ν n a
  change Measure.map (fun u : GeneralLinear.upperUnipotent n K => u * a)
      ((upperEntryProductMeasure ν n).map e.symm) = _
  rw [Measure.map_map (measurable_mul_const a) e.symm.continuous.measurable]
  have he : (fun u : GeneralLinear.upperUnipotent n K => u * a) ∘ e.symm =
      e.symm ∘ (fun X => e (e.symm X * a)) := by
    funext X
    exact (e.symm_apply_apply _).symm
  rw [he, ← Measure.map_map e.symm.continuous.measurable hp.measurable, hp.map_eq]

end RightTranslation

section Existence

variable (K : Type*) [NontriviallyNormedField K] [MeasurableSpace K] [BorelSpace K]
  [hK : LocallyCompactSpace K] [hcK : SecondCountableTopology K]

local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) K) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) K) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (r + 1) K) := borel _
local instance (r : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (r + 1) K) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r K) := borel _
local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r K) := ⟨rfl⟩

include hK hcK in
/-- Compatible measures on `N_(r+1) \ GL_(r+1)` exist for real and complex places
and, more generally, over a locally compact second countable normed field. -/
theorem quotientMeasureData_nonempty (r : ℕ) : Nonempty (QuotientMeasureData r K) := by
  let G := Langlands.GeneralLinear (r + 1) K
  let N := GeneralLinear.upperUnipotent (r + 1) K
  have : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → K))
  have : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace (Langlands.GeneralLinear (r + 1) K))
  have : SecondCountableTopology G := UnipotentClass.gl_secondCountable K (r + 1)
  let μG : Measure G := Measure.haar
  have hscalar (a : Kˣ) :
      Measure.modularCharacter (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a) = 1 := by
    let g : G := Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a
    have he : (fun x : G => x * g) = fun x => g * x :=
      funext fun x => (Matrix.GeneralLinearGroup.scalar_commute a x).symm
    have hmap : Measure.map (fun x : G => x * g) μG = μG := by
      rw [he, map_mul_left_eq_self]
    have hfactor (μ : Measure G) [μ.IsHaarMeasure] (hμ : μ = μG) :
        μ.haarScalarFactor μG = 1 := by
      subst μ
      exact Measure.haarScalarFactor_self μG
    change Measure.modularCharacterFun g = 1
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μG]
    exact hfactor _ hmap
  have hG : μG.IsMulRightInvariant := ⟨fun g => by
    have h : Measure.modularCharacterFun g = 1 :=
      Langlands.RankinSelberg.GeneralLinearUnimodularity.character_eq_one
        Measure.modularCharacter hscalar g
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul, h, one_smul]⟩
  let ν : AdditiveHaarMeasure K := ⟨Measure.addHaar, inferInstance, inferInstance⟩
  let e := upperEntryCoordinates (r + 1) (K := K)
  let μN : Measure N := (upperEntryProductMeasure ν (r + 1)).map e.symm
  have hN : μN.IsHaarMeasure := Langlands.GeneralLinear.upperEntryProductMeasure_isHaar ν
  have hNr : μN.IsMulRightInvariant := upperEntryHaar_isMulRightInvariant ν (r + 1)
  have : μN.Regular := Measure.Regular.map e.symm
  obtain ⟨μQ, hQ⟩ := QuotientIntegration.compatibleMeasureExists N
    (Langlands.GeneralLinear.UpperUnipotent.isClosed (R := K)) μG μN
  exact ⟨⟨μG, inferInstance, μN, hN, hNr, μQ, hQ⟩⟩

end Existence

end Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
