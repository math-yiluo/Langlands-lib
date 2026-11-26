import Langlands.Global.RankinSelberg.RealGapAlternateRestriction
import Langlands.Global.RankinSelberg.RealGodementColumnProduct
import Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral

/-! # Fourier transformation of the split real Godement test -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapSplitFourier

open ArchimedeanLocal (realSelfDualMeasure realFourierTransform)
open Langlands.LocalFactor.Archimedean (realScaledCharacter)
open Langlands.GodementJacquet (transposeMeasurableEquiv measurePreserving_transpose_rectangularMeasure)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure rectangularFourierIntegral rectangularPairing)
open Langlands.RankinSelberg (rectangularMeasure)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGodement (realRectangularSchwartzFourier realRectangularSchwartzFourier_apply)
open RealGapColumnFourier (columnSchwartzFourier columnSchwartzFourier_apply)

variable (k q : ℕ)
local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 1)
local notation "Vec" => I → ℝ
local notation "Sq" => Matrix I I ℝ
local notation "Leading" => Matrix I (Fin k) ℝ
local notation "Columns" => J → Vec

private abbrev columnIndex : Fin k ⊕ J ≃ Fin (k + q + 1) := finSumFinEquiv

private def splitColumns : Sq ≃ᵐ Leading × Columns :=
  let e₁ := transposeMeasurableEquiv (F := ℝ) (k + q + 1) (k + q + 1)
  let e₂ := MeasurableEquiv.piCongrLeft (fun _ => Vec) (columnIndex k q).symm
  let e₃ := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ J => Vec)
  let e₄ := (transposeMeasurableEquiv (F := ℝ) k (k + q + 1)).prodCongr (MeasurableEquiv.refl Columns)
  (e₁.trans (e₂.trans e₃)).trans e₄

private theorem splitColumns_left (X : Sq) : (splitColumns k q X).1 = fun i j => X i (j.castAdd (q + 1)) := by
  funext i j
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => Vec) (columnIndex k q).symm
    ((transposeMeasurableEquiv (F := ℝ) (k + q + 1) (k + q + 1)) X)
    ((columnIndex k q) (Sum.inl j))
  rw [Equiv.symm_apply_apply] at h
  exact congrFun h i

private theorem splitColumns_right (X : Sq) (j : J) : (splitColumns k q X).2 j = fun i => X i (j.natAdd k) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => Vec) (columnIndex k q).symm
    ((transposeMeasurableEquiv (F := ℝ) (k + q + 1) (k + q + 1)) X)
    ((columnIndex k q) (Sum.inr j))
  rwa [Equiv.symm_apply_apply] at h

private theorem measurePreserving_splitColumns (μ : AdditiveHaarMeasure ℝ) :
    MeasurePreserving (splitColumns k q) (rectangularMeasure μ (k + q + 1) (k + q + 1))
      ((rectangularMeasure μ (k + q + 1) k).prod (Measure.pi fun _ : J => rowMeasure μ (k + q + 1))) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let ν := rowMeasure μ (k + q + 1)
  have h₁ := measurePreserving_transpose_rectangularMeasure μ (k + q + 1) (k + q + 1)
  have h₂ := measurePreserving_piCongrLeft (fun _ => ν) (columnIndex k q).symm
  have h₃ := measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ J => ν)
  have h₄ := (measurePreserving_transpose_rectangularMeasure μ k (k + q + 1)).prod
    (MeasurePreserving.id (Measure.pi fun _ : J => ν))
  exact h₄.comp (h₃.comp (h₂.comp h₁))

/-- The full transform acts independently on the leading rectangle and every tail column. -/
def fourierFactors (a : ℝˣ) (T : GodementColumnFactors k q) : GodementColumnFactors k q where
  leading := realRectangularSchwartzFourier a T.leading
  tail j := columnSchwartzFourier a (T.tail j)

private theorem psi_sum {D : Type*} [Fintype D] (a : ℝˣ) (f : D → ℝ) :
    (realScaledCharacter a).complex (∑ j, f j) = ∏ j, (realScaledCharacter a).complex (f j) := by
  classical
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | @insert j s hj h => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, h]

private theorem pairing_split (X Y : Sq) : rectangularPairing Y X =
    rectangularPairing (splitColumns k q Y).1 (splitColumns k q X).1 +
      ∑ j : J, ∑ i, (splitColumns k q Y).2 j i * (splitColumns k q X).2 j i := by
  simp only [rectangularPairing, splitColumns_left, splitColumns_right]
  have h (i : I) : (∑ j, Y i j * X i j) =
      (∑ j : Fin k, Y i (j.castAdd (q + 1)) * X i (j.castAdd (q + 1))) +
        ∑ j : J, Y i (j.natAdd k) * X i (j.natAdd k) :=
    Fin.sum_univ_add (a := k) (b := q + 1) _
  simp only [h, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

/-- The positive full square transform takes split square tests to split square tests. -/
def RealGapSplitFourierStatement : Prop :=
  ∀ (a : ℝˣ) (F : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q),
    (∀ A, F A = T.squareEval k q A) →
    ∀ A, realRectangularSchwartzFourier a F A = (fourierFactors k q a T).squareEval k q A

theorem realGapSplitFourier : RealGapSplitFourierStatement k q := by
  intro a F T hT X
  let μ := realSelfDualMeasure a
  let ψ := (realScaledCharacter a).complex
  let ρ := rectangularMeasure μ (k + q + 1) k
  let σ := Measure.pi fun _ : J => rowMeasure μ (k + q + 1)
  let ν := rectangularMeasure μ (k + q + 1) (k + q + 1)
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let lead (Y : Leading) := T.leading Y * ψ (rectangularPairing Y (splitColumns k q X).1)
  let tail (j : J) (v : Vec) := T.tail j.castSucc v * ψ (∑ i, v i * (splitColumns k q X).2 j i)
  let test (p : Leading × Columns) := lead p.1 * ∏ j, tail j (p.2 j)
  have hInput (Y : Sq) : F Y * ψ (rectangularPairing Y X) = test (splitColumns k q Y) := by
    rw [pairing_split k q, AddChar.map_add_eq_mul,
      psi_sum a (fun j : J => ∑ i, (splitColumns k q Y).2 j i * (splitColumns k q X).2 j i)]
    refine (congrArg (fun z : ℂ => z * _) (hT Y)).trans ?_
    unfold GodementColumnFactors.squareEval test lead tail
    rw [Finset.prod_mul_distrib]
    simp only [splitColumns_left, splitColumns_right]
    ring
  have h := measurePreserving_splitColumns k q μ
  rw [realRectangularSchwartzFourier_apply]
  change (∫ Y, F Y * ψ (rectangularPairing Y X) ∂ν) = _
  simp only [hInput]
  calc
    _ = ∫ p, test p ∂ρ.prod σ := h.integral_comp' test
    _ = (∫ Y, lead Y ∂ρ) * ∏ j, ∫ v, tail j v ∂rowMeasure μ (k + q + 1) := by
      refine (integral_prod_mul lead (fun p : Columns => ∏ j, tail j (p j))).trans ?_
      exact congrArg ((∫ Y, lead Y ∂ρ) * ·) (integral_fintype_prod_eq_prod tail)
    _ = _ := by
      simp only [GodementColumnFactors.squareEval, fourierFactors, realRectangularSchwartzFourier_apply,
        columnSchwartzFourier_apply, realFourierTransform, ArchimedeanLocal.fourierTransform,
        rectangularFourierIntegral, lead, tail, splitColumns_left, splitColumns_right]
      rfl

end Langlands.Global.RankinSelbergGlobal.RealGapSplitFourier
