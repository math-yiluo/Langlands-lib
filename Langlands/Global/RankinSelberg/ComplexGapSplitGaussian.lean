import Langlands.Analysis.SchwartzMatrixNorm
import Langlands.Global.RankinSelberg.ComplexGapSplitPartialRestriction
import Langlands.Global.RankinSelberg.ComplexGodementGaussianProduct

/-! # Split Gaussian tests for the complex rank-gap restriction -/

noncomputable section

open MeasureTheory MvPolynomial
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapSplitGaussian

open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry operatorToEntry_apply)
open Langlands.HarmonicAnalysis (rectangularJoin rectangularJoin_castSucc rectangularJoin_last
  partialFourierPlusIntegral_join rowMeasure)
open Langlands.LocalFactor.Archimedean (complexScaledCharacter)
open ArchimedeanLocal (complexSelfDualMeasure)
open ComplexGapSplitPartialRestriction (HasSplitPartialTest)
open ComplexGapTailExchange (SplitTailTest)
open ComplexGodementColumnProduct (columnProduct_apply leadingColumns lastColumn)
open ComplexGodementGaussianPolynomial (Coordinates coordinates coordinatePartCLM
  gaussianPolynomial gaussianPolynomial_apply matrixGaussian matrixSqNorm)
open ComplexGodementGaussianProduct (columnGaussianMonomial columnGaussianMonomial_apply
  gaussianMonomial_eq_columnProduct leadingExponents)
open ComplexGodementPartialFourier (partialSchwartz_apply)

local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ

private def columnFactor {m n : ℕ} (d : Coordinates m n →₀ ℕ) (j : Fin n) : 𝓢(Fin m → ℂ, ℂ) :=
  columnGaussianMonomial fun i => d (i.1, j, i.2)

private theorem gaussianMonomial_columnFactors {m n : ℕ} (d : Coordinates m n →₀ ℕ)
    (c : ℂ) (A : Mat m n) :
    gaussianPolynomial (monomial d c) A = c * ∏ j, columnFactor d j (fun i => A i j) := by
  have hprod : (∏ i, coordinates A i ^ d i) =
      ∏ j : Fin n, ∏ i : Fin m × Bool, coordinatePartCLM i.2 (A i.1 j) ^ d (i.1, j, i.2) := by
    simp only [Fintype.prod_prod_type, coordinates]
    rw [Finset.prod_comm]
  have hGauss : matrixGaussian A = ∏ j : Fin n, (Real.exp (-∑ i, ‖A i j‖ ^ 2) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    unfold matrixGaussian matrixSqNorm
    rw [Finset.sum_neg_distrib, Finset.sum_comm]
  have hMonomial : eval (coordinates A) (monomial d c) = c * ∏ i, coordinates A i ^ d i := by
    rw [eval_monomial, Finsupp.prod_fintype]
    exact fun i => pow_zero (coordinates A i)
  rw [gaussianPolynomial_apply, hMonomial, hprod, hGauss]
  simp only [columnFactor, columnGaussianMonomial_apply, Finset.prod_mul_distrib]
  rw [mul_assoc]

variable (k q : ℕ)

local notation "Size" => (k + q + 1)
local notation "Top" => Fin (k + q + 1)
local notation "Square" => Mat (k + q + 1) (k + q + 1)
local notation "Rect" => Mat (k + q + 1) (k + q + 2)
local notation "Exp" => (Coordinates Size (Size + 1) →₀ ℕ)

private def leadingBlockExponents (d : Coordinates Size Size →₀ ℕ) : Coordinates Size k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => d (i.1, i.2.1.castAdd (q + 1), i.2.2)

/-- The leading Gaussian rectangle, the physical tail columns and the final column transform
of a Gaussian monomial. -/
def splitGaussianMonomial (a : ℂˣ) (d : Exp) (c : ℂ) : SplitTailTest k q where
  leading A := gaussianPolynomial (monomial (leadingBlockExponents k q (leadingExponents d)) c) A
  first x := columnFactor (leadingExponents d) ((0 : Fin (q + 1)).natAdd k) x
  later j := columnFactor (leadingExponents d) (j.succ.natAdd k)
  lastFrequency v := ComplexGodementFourier.fourier a (columnFactor d (Fin.last Size)) v

open scoped Matrix.Norms.Elementwise in
/-- The leading rectangle, first column and last frequency of a split Gaussian
have Schwartz representatives for the entrywise matrix norm. -/
theorem splitGaussianMonomial_schwartz (a : ℂˣ) (d : Exp) (c : ℂ) :
    ∃ (L : 𝓢(Mat Size k, ℂ)) (F G : 𝓢(Top → ℂ, ℂ)),
      (splitGaussianMonomial k q a d c).leading = L.toFun ∧
      (splitGaussianMonomial k q a d c).first = F.toFun ∧
      (splitGaussianMonomial k q a d c).lastFrequency = G.toFun := by
  obtain ⟨G, hG⟩ := ComplexGodementFourier.exists_schwartz_fourier a (columnFactor d (Fin.last Size))
  refine ⟨operatorToEntry (gaussianPolynomial (monomial
    (leadingBlockExponents k q (leadingExponents d)) c)),
    columnFactor (leadingExponents d) ((0 : Fin (q + 1)).natAdd k), G, ?_, rfl, ?_⟩
  · funext A
    exact (operatorToEntry_apply _ A).symm
  · exact hG.symm

private theorem splitGaussian_leading_square (a : ℂˣ) (d : Exp) (c : ℂ) (A : Square) :
    let T := splitGaussianMonomial k q a d c
    gaussianPolynomial (monomial (leadingExponents d) c) A =
      T.leading (fun i j => A i (j.castAdd (q + 1))) *
        T.first (fun i => A i ((0 : Fin (q + 1)).natAdd k)) *
        ∏ j : Fin q, T.later j (fun i => A i (j.succ.natAdd k)) := by
  let f (j : Top) := columnFactor (leadingExponents d) j (fun i => A i j)
  let A₀ : Mat Size k := fun i j => A i (j.castAdd (q + 1))
  let d₀ := leadingBlockExponents k q (leadingExponents d)
  let h (j : Fin (q + 1)) := f (j.natAdd k)
  let c₀ := ∏ j : Fin k, f (j.castAdd (q + 1))
  have hLeading : gaussianPolynomial (monomial d₀ c) A₀ = c * c₀ :=
    gaussianMonomial_columnFactors d₀ c A₀
  change _ = gaussianPolynomial (monomial d₀ c) A₀ * h 0 * ∏ j : Fin q, h j.succ
  calc
    _ = c * ∏ j, f j := gaussianMonomial_columnFactors (leadingExponents d) c A
    _ = c * (c₀ * ∏ j, h j) :=
      congrArg (c * ·) (Fin.prod_univ_add (a := k) (b := q + 1) f)
    _ = c * (c₀ * (h 0 * ∏ j : Fin q, h j.succ)) :=
      congrArg (fun z => c * (c₀ * z)) (Fin.prod_univ_succ h)
    _ = (c * c₀) * h 0 * ∏ j : Fin q, h j.succ := by ring
    _ = _ := congrArg (fun z => z * h 0 * ∏ j : Fin q, h j.succ) hLeading.symm

/-- The explicit split test satisfies the alternate restriction's partial Fourier premise. -/
def ComplexGapSplitGaussianStatement : Prop :=
  ∀ (a : ℂˣ) (d : Exp) (c : ℂ),
    HasSplitPartialTest k q a (operatorToEntry (gaussianPolynomial (monomial d c)))
      (splitGaussianMonomial k q a d c)

theorem complexGapSplitGaussian : ComplexGapSplitGaussianStatement k q := by
  intro a d c A v
  rw [partialSchwartz_apply, partialFourierPlusIntegral_join]
  simp_rw [operatorToEntry_apply, gaussianMonomial_eq_columnProduct, columnProduct_apply]
  have hLead (u : Top → ℂ) : leadingColumns (rectangularJoin A u) = A := by
    ext i j
    exact rectangularJoin_castSucc A u i j
  have hLast (u : Top → ℂ) : lastColumn (rectangularJoin A u) = u :=
    funext fun i => rectangularJoin_last A u i
  simp_rw [hLead, hLast, mul_assoc, integral_const_mul]
  have hFreq : (∫ u : Top → ℂ, columnFactor d (Fin.last Size) u *
      (complexScaledCharacter a).complex (∑ i, v i * u i) ∂rowMeasure (complexSelfDualMeasure a) Size) =
      (splitGaussianMonomial k q a d c).lastFrequency v := by
    unfold splitGaussianMonomial ComplexGodementFourier.fourier
    exact integral_congr_ae (ae_of_all _ fun u => by simp only [mul_comm (v _)])
  calc
    _ = gaussianPolynomial (monomial (leadingExponents d) c) A *
        (splitGaussianMonomial k q a d c).lastFrequency v :=
      congrArg (gaussianPolynomial (monomial (leadingExponents d) c) A * ·) hFreq
    _ = _ := by
      rw [splitGaussian_leading_square k q a d c A]
      ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapSplitGaussian
