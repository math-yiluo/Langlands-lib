import Langlands.Global.RankinSelberg.ComplexJacquetUnipotentMeasure
import Langlands.Representation.RankinSelberg.Measures
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Splitting the first unipotent column in the larger-rank-gap chart -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapRectangleShear

open Langlands.GeneralLinear (upperUnipotent)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)

variable (k q : ℕ)

local notation "Head" => Fin k → ℂ
local notation "Tail" => Matrix (Fin k) (Fin q) ℂ
local notation "Rect" => Matrix (Fin k) (Fin (q + 1)) ℂ
local notation "N" => upperUnipotent (q + 1) ℂ

local instance rectangleShearMeasurable : MeasurableSpace N := borel _
local instance rectangleShearBorel : BorelSpace N := ⟨rfl⟩
local instance rectangleShearAdd : MeasurableAdd₂ Tail :=
  inferInstanceAs (MeasurableAdd₂ (Fin k → Fin q → ℂ))
local instance rectangleShearSub : MeasurableSub₂ Tail :=
  inferInstanceAs (MeasurableSub₂ (Fin k → Fin q → ℂ))

/-- Split the first column from the rest of the rectangle. -/
def splitRectangle : Rect ≃ᵐ Head × Tail :=
  (MeasurableEquiv.piCongrRight fun _ : Fin k =>
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 1) => ℂ) 0).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℂ (Fin q → ℂ) (Fin k))

theorem splitRectangle_apply (Y : Rect) :
    splitRectangle k q Y = (fun i => Y i 0, fun i j => Y i j.succ) := by
  apply Prod.ext rfl
  ext i j
  change Y i ((0 : Fin (q + 1)).succAbove j) = Y i j.succ
  rw [Fin.succAbove_zero]

/-- The product of scalar measures is preserved by separating the first column. -/
theorem measurePreserving_splitRectangle (μ : AdditiveHaarMeasure ℂ) :
    MeasurePreserving (splitRectangle k q) (rectangularMeasure μ k (q + 1))
      ((rowMeasure μ k).prod (rectangularMeasure μ k q)) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  exact (measurePreserving_arrowProdEquivProdArrow ℂ (Fin q → ℂ) (Fin k) (fun _ => μ.measure)
      (fun _ => Measure.pi fun _ : Fin q => μ.measure)).comp
    (measurePreserving_pi _ _ fun _ =>
      measurePreserving_piFinSuccAbove (fun _ : Fin (q + 1) => μ.measure) 0)

/-- The rank-one correction from placing the first column shear before the tail unipotent. -/
def firstRowCorrection (x : Head) (Z : N) : Tail :=
  fun i j => x i * Z.val.val 0 j.succ

private theorem measurable_firstRowCorrection : Measurable (fun p : Head × N => firstRowCorrection k q p.1 p.2) := by
  have hp : Measurable (fun z : N => z.val.val) :=
    (Units.continuous_val.comp continuous_subtype_val).measurable
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    ((measurable_pi_apply j.succ).comp ((measurable_pi_apply 0).comp (hp.comp measurable_snd)))

private def shear : ((Head × N) × Tail) ≃ᵐ ((Head × N) × Tail) where
  toFun p := (p.1, p.2 - firstRowCorrection k q p.1.1 p.1.2)
  invFun p := (p.1, p.2 + firstRowCorrection k q p.1.1 p.1.2)
  left_inv p := Prod.ext rfl (sub_add_cancel p.2 (firstRowCorrection k q p.1.1 p.1.2))
  right_inv p := Prod.ext rfl (add_sub_cancel_right p.2 (firstRowCorrection k q p.1.1 p.1.2))
  measurable_toFun := measurable_fst.prodMk
    (measurable_snd.sub ((measurable_firstRowCorrection k q).comp measurable_fst))
  measurable_invFun := measurable_fst.prodMk
    (measurable_snd.add ((measurable_firstRowCorrection k q).comp measurable_fst))

private theorem measurePreserving_shear (μ : AdditiveHaarMeasure ℂ) :
    let ξ := (rowMeasure μ k).prod (entryHaar μ (q + 1))
    let ν := rectangularMeasure μ k q
    MeasurePreserving (shear k q) (ξ.prod ν) (ξ.prod ν) := by
  intro ξ ν
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : ν.IsAddHaarMeasure := rectangularMeasure_isAddHaar μ k q
  let : SigmaFinite (entryHaar μ (q + 1)) := entryHaar_sigmaFinite μ _
  exact (MeasurePreserving.id ξ).skew_product (g :=
    fun (p : Head × N) (Y : Tail) => Y - firstRowCorrection k q p.1 p.2)
    (measurable_snd.sub ((measurable_firstRowCorrection k q).comp measurable_fst))
    (ae_of_all _ fun p => by
      simp only [sub_eq_add_neg]
      exact map_add_right_eq_self ν _)

/-- Split the first column and translate the later entries by its tail correction. -/
def splitTailRectangle : Rect × N ≃ᵐ Head × (Tail × N) :=
  let swap := MeasurableEquiv.refl Head |>.prodCongr (MeasurableEquiv.prodComm : Tail × N ≃ᵐ N × Tail)
  let e := ((splitRectangle k q).prodCongr (MeasurableEquiv.refl N)).trans MeasurableEquiv.prodAssoc
  e.trans (swap.trans (MeasurableEquiv.prodAssoc.symm.trans
    ((shear k q).trans (MeasurableEquiv.prodAssoc.trans swap.symm))))

theorem splitTailRectangle_apply (Y : Rect) (Z : N) :
    splitTailRectangle k q (Y, Z) = (fun i => Y i 0,
      (fun i j => Y i j.succ - firstRowCorrection k q (fun l => Y l 0) Z i j), Z) := by
  change ((splitRectangle k q Y).1, (splitRectangle k q Y).2 -
    firstRowCorrection k q (splitRectangle k q Y).1 Z, Z) = _
  rw [splitRectangle_apply]
  rfl

/-- The corrected split separates the first column from the exchange variables in the
product of the rectangle measure and the tail entry Haar measure. -/
def ComplexGapRectangleShearStatement : Prop :=
  ∀ μ : AdditiveHaarMeasure ℂ,
    let η := entryHaar μ (q + 1)
    MeasurePreserving (splitTailRectangle k q) ((rectangularMeasure μ k (q + 1)).prod η)
      ((rowMeasure μ k).prod ((rectangularMeasure μ k q).prod η))

theorem complexGapRectangleShear : ComplexGapRectangleShearStatement k q := by
  intro μ η
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let ξ := rowMeasure μ k
  let ν := rectangularMeasure μ k q
  have he := (measurePreserving_prodAssoc ξ ν η).comp
    ((measurePreserving_splitRectangle k q μ).prod (MeasurePreserving.id η))
  have hswap : MeasurePreserving
      ((MeasurableEquiv.refl Head).prodCongr (MeasurableEquiv.prodComm : Tail × N ≃ᵐ N × Tail))
      (ξ.prod (ν.prod η)) (ξ.prod (η.prod ν)) :=
    (MeasurePreserving.id ξ).prod measurePreserving_swap
  have ha := measurePreserving_prodAssoc ξ η ν
  exact ((hswap.symm _).comp (ha.comp ((measurePreserving_shear k q μ).comp ((ha.symm _).comp hswap)))).comp he

end Langlands.Global.RankinSelbergGlobal.ComplexGapRectangleShear
