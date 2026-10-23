import Langlands.Group.GL.IntegralSubgroup
import Langlands.Group.GL.BlockUnipotent
import Langlands.Group.GL.RankMaps
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! # The concrete Iwasawa measure equation in Shahidi's normalization -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Langlands.Shahidi

universe uF

variable {F : Type uF} [Field F]

/-- The last-column unipotent matrix with the supplied column coordinates. -/
def lastColumnUnipotent (n : ℕ) (x : Fin n → F) : GeneralLinear (n + 1) F :=
  GeneralLinear.blockUnipotent (a := n) (b := 1) rfl (fun i _ => x i)

@[simp] theorem lastColumnUnipotent_zero (n : ℕ) :
    lastColumnUnipotent n (0 : Fin n → F) = 1 :=
  GeneralLinear.blockUnipotent_zero rfl

theorem lastColumnUnipotent_add (n : ℕ) (x y : Fin n → F) :
    lastColumnUnipotent n (x + y) =
      lastColumnUnipotent n x * lastColumnUnipotent n y :=
  GeneralLinear.blockUnipotent_add rfl _ _

@[simp] theorem lastColumnUnipotent_entry (n : ℕ) (x : Fin n → F) (i : Fin n) :
    lastColumnUnipotent n x (i.castAdd 1) ((0 : Fin 1).natAdd n) = x i := by
  change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (fun i (_ : Fin 1) => x i)
    0 1 (finSumFinEquiv.symm (i.castAdd 1))
    (finSumFinEquiv.symm ((0 : Fin 1).natAdd n)) = _
  simp
  rfl

variable (O : Subring F) (n : ℕ)

/-- The actual multiplication map `(x,a,z,k) ↦ u(x) diag(a,1) z k`.
The scalar `z` is embedded in the center of the larger general linear group. -/
def iwasawaMeasureMap
    (p : (((Fin n → F) × GeneralLinear n F) × Fˣ) ×
      GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O) :
    GeneralLinear (n + 1) F :=
  lastColumnUnipotent n p.1.1.1 *
    GeneralLinear.rankInclusion 1 p.1.1.2 *
      GeneralLinear.scalar p.1.2 * p.2.val

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_lastColumnUnipotent :
    Continuous (lastColumnUnipotent (F := F) n) :=
  (GeneralLinear.continuous_blockUnipotent rfl).comp
    (continuous_pi fun i => continuous_pi fun _ => continuous_apply i)

theorem continuous_iwasawaMeasureMap :
    Continuous (iwasawaMeasureMap O n) :=
  ((((continuous_lastColumnUnipotent n).comp
      (continuous_fst.fst.fst)).mul
    ((GeneralLinear.rankInclusionContinuous 1).continuous.comp
      (continuous_fst.fst.snd))).mul
    (GeneralLinear.scalarContinuous.continuous.comp (continuous_fst.snd))).mul
    (continuous_subtype_val.comp continuous_snd)

end Topology

section Measures

variable [MeasurableSpace F] [MeasurableSpace Fˣ]
  [MeasurableSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear (n + 1) F)]
  [MeasurableSpace (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O)]

/-- The measure in Iwasawa coordinates, including the inverse determinant
weight on the smaller general linear block. -/
def iwasawaCoordinateMeasure (abv : AbsoluteValue F ℝ)
    (dn₂ : Measure (Fin n → F)) (daStar : Measure (GeneralLinear n F))
    (dzStar : Measure Fˣ)
    (dk : Measure (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O)) :
    Measure ((((Fin n → F) × GeneralLinear n F) × Fˣ) ×
      GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O) :=
  (((dn₂.prod daStar).prod dzStar).prod dk).withDensity
    (fun p => ENNReal.ofReal ((abv
      (p.1.1.2 : Matrix (Fin n) (Fin n) F).det)⁻¹))

/-- Push the actual weighted product measure through Iwasawa multiplication.
This construction alone does not assert Haar invariance or compatibility. -/
def iwasawaMeasureFromFactors (abv : AbsoluteValue F ℝ)
    (dn₂ : Measure (Fin n → F)) (daStar : Measure (GeneralLinear n F))
    (dzStar : Measure Fˣ)
    (dk : Measure (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O)) :
    Measure (GeneralLinear (n + 1) F) :=
  Measure.map (iwasawaMeasureMap O n)
    (iwasawaCoordinateMeasure O n abv dn₂ daStar dzStar dk)

/-- Item 4's measure equation and equality of compact integral-group
volumes. These are conditions on supplied measures, not existence assumptions
hidden in a chosen measure or a representation. -/
def IsIwasawaMeasureCompatible (abv : AbsoluteValue F ℝ)
    (dn₂ : Measure (Fin n → F)) (daStar : Measure (GeneralLinear n F))
    (dzStar : Measure Fˣ)
    (dk : Measure (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O))
    (dgStar : Measure (GeneralLinear (n + 1) F)) : Prop :=
  dgStar = iwasawaMeasureFromFactors O n abv dn₂ daStar dzStar dk ∧
    dgStar (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O) = dk Set.univ

/-- Evaluation of the weighted pushforward on a measurable set. -/
theorem iwasawaMeasureFromFactors_apply (abv : AbsoluteValue F ℝ)
    (dn₂ : Measure (Fin n → F)) (daStar : Measure (GeneralLinear n F))
    (dzStar : Measure Fˣ)
    (dk : Measure (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O))
    (hmap : Measurable (iwasawaMeasureMap O n))
    {S : Set (GeneralLinear (n + 1) F)} (hS : MeasurableSet S) :
    iwasawaMeasureFromFactors O n abv dn₂ daStar dzStar dk S =
      ∫⁻ p in iwasawaMeasureMap O n ⁻¹' S,
        ENNReal.ofReal ((abv (p.1.1.2 : Matrix (Fin n) (Fin n) F).det)⁻¹)
        ∂(((dn₂.prod daStar).prod dzStar).prod dk) := by
  rw [iwasawaMeasureFromFactors, Measure.map_apply hmap hS,
    iwasawaCoordinateMeasure, withDensity_apply _ (hmap hS)]

end Measures

end Langlands.Shahidi
