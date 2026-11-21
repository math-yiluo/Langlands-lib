import Langlands.Global.RankinSelberg.ComplexGapAlternateRestriction
import Langlands.Global.RankinSelberg.ComplexGapLeadingFourier
import Langlands.Representation.GodementJacquet.ComplexRectangularFourierCovariance

/-! # Fourier transformation of the split Godement test -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapSplitFourier

open ArchimedeanLocal (complexSelfDualMeasure)
open Langlands.GodementJacquet (complexRectangularFourier transposeMeasurableEquiv
  measurePreserving_transpose_rectangularMeasure)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.RankinSelberg (rectangularMeasure)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapLeadingFourier (rectTransform rectTransform_apply)
open ComplexGodementFourier (piMeasure psi rectFourier)

variable (k q : ℕ)
local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 2)
local notation "Vec" => I → ℂ
local notation "Rect" => Matrix I (Fin (k + q + 2)) ℂ
local notation "Leading" => Matrix I (Fin k) ℂ
local notation "Columns" => J → Vec

private abbrev columnIndex : Fin k ⊕ J ≃ Fin (k + q + 2) := finSumFinEquiv

private def splitColumns : Rect ≃ᵐ Leading × Columns :=
  let e₁ := transposeMeasurableEquiv (F := ℂ) (k + q + 1) (k + q + 2)
  let e₂ := MeasurableEquiv.piCongrLeft (fun _ => Vec) (columnIndex k q).symm
  let e₃ := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ J => Vec)
  let e₄ := (transposeMeasurableEquiv (F := ℂ) k (k + q + 1)).prodCongr (MeasurableEquiv.refl Columns)
  (e₁.trans (e₂.trans e₃)).trans e₄

private theorem splitColumns_left (X : Rect) : (splitColumns k q X).1 = fun i j => X i (j.castAdd (q + 2)) := by
  funext i j
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => Vec) (columnIndex k q).symm
    ((transposeMeasurableEquiv (F := ℂ) (k + q + 1) (k + q + 2)) X)
    ((columnIndex k q) (Sum.inl j))
  rw [Equiv.symm_apply_apply] at h
  exact congrFun h i

private theorem splitColumns_right (X : Rect) (j : J) : (splitColumns k q X).2 j = fun i => X i (j.natAdd k) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => Vec) (columnIndex k q).symm
    ((transposeMeasurableEquiv (F := ℂ) (k + q + 1) (k + q + 2)) X)
    ((columnIndex k q) (Sum.inr j))
  rwa [Equiv.symm_apply_apply] at h

private theorem measurePreserving_splitColumns (μ : AdditiveHaarMeasure ℂ) :
    MeasurePreserving (splitColumns k q) (rectangularMeasure μ (k + q + 1) (k + q + 2))
      ((rectangularMeasure μ (k + q + 1) k).prod (Measure.pi fun _ : J => rowMeasure μ (k + q + 1))) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let ν := rowMeasure μ (k + q + 1)
  have h₁ := measurePreserving_transpose_rectangularMeasure μ (k + q + 1) (k + q + 2)
  have h₂ := measurePreserving_piCongrLeft (fun _ => ν) (columnIndex k q).symm
  have h₃ := measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ J => ν)
  have h₄ := (measurePreserving_transpose_rectangularMeasure μ k (k + q + 1)).prod
    (MeasurePreserving.id (Measure.pi fun _ : J => ν))
  exact h₄.comp (h₃.comp (h₂.comp h₁))

/-- The positive trace Fourier transform as a column Schwartz function. -/
def columnTransform {d : ℕ} (a : ℂˣ) (φ : 𝓢(Fin d → ℂ, ℂ)) : 𝓢(Fin d → ℂ, ℂ) :=
  Classical.choose (ComplexGodementFourier.exists_schwartz_fourier a φ)

@[simp] theorem columnTransform_apply {d : ℕ} (a : ℂˣ) (φ : 𝓢(Fin d → ℂ, ℂ)) (x : Fin d → ℂ) :
    columnTransform a φ x = ComplexGodementFourier.fourier a φ x :=
  congrFun (Classical.choose_spec (ComplexGodementFourier.exists_schwartz_fourier a φ)) x

/-- Transforming a column with the opposite character recovers the original test. -/
theorem fourier_columnTransform_neg {d : ℕ} (a : ℂˣ) (φ : 𝓢(Fin d → ℂ, ℂ)) (x : Fin d → ℂ) :
    ComplexGodementFourier.fourier (-a) (columnTransform a φ) x = φ x := by
  have h : (columnTransform a φ : (Fin d → ℂ) → ℂ) = ComplexGodementFourier.fourier a φ :=
    funext (columnTransform_apply a φ)
  rw [h]
  apply ComplexGodementFourier.fourier_neg_fourier a φ.continuous φ.integrable
  rw [← h]
  exact (columnTransform a φ).integrable

/-- The full transform acts independently on the leading rectangle and every tail column. -/
def fourierFactors (a : ℂˣ) (T : GodementColumnFactors k q) : GodementColumnFactors k q where
  leading := rectTransform a T.leading
  tail j := columnTransform a (T.tail j)

private theorem psi_sum {D : Type*} [Fintype D] (a : ℂˣ) (f : D → ℂ) :
    psi a (∑ j, f j) = ∏ j, psi a (f j) := by
  classical
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | @insert j s hj h => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, h]

private theorem pairing_split (X Y : Rect) : (∑ i, ∑ j, Y i j * X i j) =
    (∑ i, ∑ j, (splitColumns k q Y).1 i j * (splitColumns k q X).1 i j) +
      ∑ j : J, ∑ i, (splitColumns k q Y).2 j i * (splitColumns k q X).2 j i := by
  simp only [splitColumns_left, splitColumns_right]
  have h (i : I) : (∑ j, Y i j * X i j) =
      (∑ j : Fin k, Y i (j.castAdd (q + 2)) * X i (j.castAdd (q + 2))) +
        ∑ j : J, Y i (j.natAdd k) * X i (j.natAdd k) :=
    Fin.sum_univ_add (a := k) (b := q + 2) _
  simp only [h, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

/-- The positive full rectangular transform takes split tests to split tests. -/
def ComplexGapSplitFourierStatement : Prop :=
  ∀ (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (T : GodementColumnFactors k q),
    (∀ X, Φ X = T.eval k q X) →
    ∀ X, rectTransform a Φ X = (fourierFactors k q a T).eval k q X

theorem complexGapSplitFourier : ComplexGapSplitFourierStatement k q := by
  intro a Φ T hT X
  let μ := complexSelfDualMeasure a
  let ρ := rectangularMeasure μ (k + q + 1) k
  let σ := Measure.pi fun _ : J => rowMeasure μ (k + q + 1)
  let ν := rectangularMeasure μ (k + q + 1) (k + q + 2)
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let lead (Y : Leading) := T.leading Y * psi a (∑ i, ∑ j, Y i j * (splitColumns k q X).1 i j)
  let tail (j : J) (v : Vec) := T.tail j v * psi a (∑ i, v i * (splitColumns k q X).2 j i)
  let test (p : Leading × Columns) := lead p.1 * ∏ j, tail j (p.2 j)
  have hInput (Y : Rect) : Φ Y * psi a (∑ i, ∑ j, Y i j * X i j) = test (splitColumns k q Y) := by
    rw [pairing_split k q, AddChar.map_add_eq_mul,
      psi_sum a (fun j : J => ∑ i, (splitColumns k q Y).2 j i * (splitColumns k q X).2 j i)]
    refine (congrArg (fun z : ℂ => z * _) (hT Y)).trans ?_
    unfold GodementColumnFactors.eval test lead tail
    rw [Finset.prod_mul_distrib]
    simp only [splitColumns_left, splitColumns_right]
    ring
  have h := measurePreserving_splitColumns k q μ
  rw [rectTransform_apply]
  change (∫ Y, Φ Y * psi a (∑ i, ∑ j, Y i j * X i j) ∂ν) = _
  simp only [hInput]
  calc
    _ = ∫ p, test p ∂ρ.prod σ := h.integral_comp' test
    _ = (∫ Y, lead Y ∂ρ) * ∏ j, ∫ v, tail j v ∂rowMeasure μ (k + q + 1) := by
      refine (integral_prod_mul lead (fun p : Columns => ∏ j, tail j (p j))).trans ?_
      exact congrArg ((∫ Y, lead Y ∂ρ) * ·) (integral_fintype_prod_eq_prod tail)
    _ = _ := by
      simp only [GodementColumnFactors.eval, fourierFactors, rectTransform_apply, rectFourier,
        columnTransform_apply, ComplexGodementFourier.fourier, lead, tail, splitColumns_left, splitColumns_right]
      rfl

/-- The split transform uses the rectangular Fourier function in the Godement reflection. -/
theorem rectTransform_eq_complexRectangularFourier (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) :
    (rectTransform a Φ : Rect → ℂ) = complexRectangularFourier a Φ := by
  funext X
  rw [rectTransform_apply]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGapSplitFourier
