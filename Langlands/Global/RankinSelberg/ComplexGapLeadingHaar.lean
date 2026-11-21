import Langlands.Global.RankinSelberg.ComplexGapDualChart

/-! # Separating the leading Haar variable in the normalized chart -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapLeadingHaar

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open ComplexGapDualChart (retainedTail)
open ComplexGapTriangularChart (Outer outerMeasure diagonalWeightMeasure)
open ComplexGapUnitDeterminant (normalizationWeight measurable_normalizationWeight unitOuterMeasure)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ

local instance gapLeadingHaarGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapLeadingHaarGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

variable (k q : ℕ)
local notation "Size" => k + q + 1
local notation "Y" => Fin (q + 1) → ℝ
local notation "Head" => Fin k → ℂ

/-- The logarithmic tail, compact matrix and first rectangular column. -/
abbrev Retained := (Y × KU Size) × Head

/-- Product coordinates separating the leading group from the retained data. -/
def splitOuter : Outer k q ≃ᵐ G k × Retained k q :=
  (MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc (MeasurableEquiv.refl Head)).trans
    MeasurableEquiv.prodAssoc

/-- The outer tuple assembled from the leading matrix and retained data. -/
def outerWithLeading (h : G k) (p : Retained k q) : Outer k q := (((h, p.1.1), p.1.2), p.2)

@[simp] theorem splitOuter_apply (p : Outer k q) :
    splitOuter k q p = (p.1.1.1, (p.1.1.2, p.1.2), p.2) := rfl

@[simp] theorem splitOuter_symm_apply (h : G k) (p : Retained k q) :
    (splitOuter k q).symm (h, p) = outerWithLeading k q h p := rfl

/-- The retained matrix depends on the retained data and the upper unipotent, independently of the leading Haar variable. -/
theorem retainedTail_outerWithLeading (h : G k) (p : Retained k q) (Z : N (q + 1)) :
    retainedTail k q (outerWithLeading k q h p) Z = retainedTail k q (outerWithLeading k q 1 p) Z := rfl

private def normalizedDiagonal : Measure Y :=
  (diagonalWeightMeasure k q).withDensity (fun y => (normalizationWeight k q y : ℝ≥0∞))

/-- The outer measure with the leading matrix factored out. -/
def retainedMeasure (μ : AdditiveHaarMeasure ℂ) (κ : Measure (KU Size)) : Measure (Retained k q) :=
  ((normalizedDiagonal k q).prod κ).prod (rowMeasure μ k)

/-- The measure on the retained data is sigma finite. -/
theorem sigmaFinite_retainedMeasure (μ : AdditiveHaarMeasure ℂ) (κ : Measure (KU Size))
    [κ.IsHaarMeasure] : SigmaFinite (retainedMeasure k q μ κ) := by
  let : CompactSpace (KU Size) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite (normalizedDiagonal k q) := SigmaFinite.withDensity _
  unfold retainedMeasure
  infer_instance

/-- Separating the leading matrix preserves the normalized outer measure. -/
def ComplexGapLeadingHaarStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (κ : Measure (KU Size)), κ.IsHaarMeasure →
    MeasurePreserving (splitOuter k q) (unitOuterMeasure k q μ κ)
      ((complexGeneralLinearHaar k).prod (retainedMeasure k q μ κ))

theorem complexGapLeadingHaar : ComplexGapLeadingHaarStatement k q := by
  intro μ κ hκ
  let : κ.IsHaarMeasure := hκ
  let : CompactSpace (KU Size) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let σ := complexGeneralLinearHaar k
  let ν := normalizedDiagonal k q
  let η := rowMeasure μ k
  let : SigmaFinite ν := SigmaFinite.withDensity _
  have hσ : unitOuterMeasure k q μ κ = (((σ.prod ν).prod κ).prod η) := by
    let θ (y : Y) : ℝ≥0∞ := normalizationWeight k q y
    have hθ : Measurable θ := measurable_normalizationWeight k q
    have hθ₁ : Measurable (fun p : G k × Y => θ p.2) := hθ.comp measurable_snd
    have hθ₂ : Measurable (fun p : (G k × Y) × KU Size => θ p.1.2) :=
      hθ₁.comp measurable_fst
    change ((((σ.prod (diagonalWeightMeasure k q)).prod κ).prod η).withDensity fun p => θ p.1.1.2) =
      (((σ.prod ((diagonalWeightMeasure k q).withDensity θ)).prod κ).prod η)
    rw [prod_withDensity_right hθ, prod_withDensity_left hθ₁, prod_withDensity_left hθ₂]
  rw [hσ]
  exact (measurePreserving_prodAssoc σ (ν.prod κ) η).comp
    ((measurePreserving_prodAssoc σ ν κ).prod (MeasurePreserving.id η))

section Interchange

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

/-- Move the middle variable to the last factor of a product. -/
def interchangeMiddle : (A × C) × B ≃ᵐ A × (B × C) :=
  MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl A) MeasurableEquiv.prodComm)

/-- Product Haar measures are unchanged by reassociation and permutation of factors. -/
theorem measurePreserving_interchangeMiddle (μ : Measure A) (ν : Measure B) (η : Measure C)
    [SFinite μ] [SFinite ν] [SFinite η] : MeasurePreserving (interchangeMiddle (A := A) (B := B) (C := C))
      ((μ.prod η).prod ν) (μ.prod (ν.prod η)) :=
  ((MeasurePreserving.id μ).prod measurePreserving_swap).comp (measurePreserving_prodAssoc μ η ν)

/-- Swap the first two variables of a right-associated product. -/
def interchangeFirst : A × (B × C) ≃ᵐ B × (A × C) :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl C)).trans MeasurableEquiv.prodAssoc)

/-- Interchanging the first two factors preserves the product measure. -/
theorem measurePreserving_interchangeFirst (μ : Measure A) (ν : Measure B) (η : Measure C)
    [SFinite μ] [SFinite ν] [SFinite η] : MeasurePreserving (interchangeFirst (A := A) (B := B) (C := C))
      (μ.prod (ν.prod η)) (ν.prod (μ.prod η)) :=
  (measurePreserving_prodAssoc ν μ η).comp
    ((measurePreserving_swap.prod (MeasurePreserving.id η)).comp ((measurePreserving_prodAssoc μ ν η).symm _))

end Interchange

end Langlands.Global.RankinSelbergGlobal.ComplexGapLeadingHaar
