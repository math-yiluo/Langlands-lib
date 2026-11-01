import Langlands.HarmonicAnalysis.RectangularFourierCommutationProof
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct

/-! Fixing the last column cancels the opposite Fourier transforms on that column. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [T2Space K] {n : ℕ}

/-- Restrict a rectangular test function to a fixed final column. -/
def rectangularFixedLastColumn (b : Fin n → K) :
    SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) →ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin n) (Fin n) K) where
  toFun Φ := SchwartzBruhat.compLeftInverse Φ
    (fun A => rectangularJoin A b) rectangularFirstColumns
    (continuous_rectangularJoin.comp (continuous_id.prodMk continuous_const))
    continuous_rectangularFirstColumns (fun A => rectangularFirstColumns_join A b)
  map_add' Φ Ψ := by ext A; rfl
  map_smul' c Φ := by ext A; rfl

omit [Field K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
@[simp] theorem rectangularFixedLastColumn_apply
    (b : Fin n → K) (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (A : Matrix (Fin n) (Fin n) K) :
    rectangularFixedLastColumn b Φ A = Φ (rectangularJoin A b) := rfl

omit [Field K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
/-- The fixed-column slice of an entry tensor is a scalar times its square tensor. -/
theorem rectangularFixedLastColumn_entryProduct
    (b : Fin n → K) (g : Fin n → Fin (n + 1) → SchwartzBruhat K) :
    rectangularFixedLastColumn b (entryProductTest g) =
      (∏ i, g i (Fin.last n) (b i)) • entryProductTest (fun i j => g i j.castSucc) := by
  ext A
  simp only [rectangularFixedLastColumn_apply, entryProductTest_apply,
    Fin.prod_univ_castSucc, rectangularJoin_castSucc, rectangularJoin_last,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  exact mul_comm _ _

variable [LocallyCompactSpace K] [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
  (hsd : IsSelfDual ψ ν)

private theorem full_partial_entryProduct
    (g : Fin n → Fin (n + 1) → SchwartzBruhat K)
    (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K) :
    rectangularFourierEquiv ψ ν n (n + 1) hsd
        (partialFourierEquiv ψ ν n hsd (entryProductTest g)) (rectangularJoin A b) =
      rectangularFourierEquiv ψ ν n n hsd
        (rectangularFixedLastColumn b (entryProductTest g)) A := by
  have : SigmaFinite ν.measure := selfDualSigmaFinite K ψ ν hsd
  let g' : Fin n → Fin (n + 1) → K → ℂ := fun i j =>
    Fin.lastCases (fun t => fourierIntegral ψ ν (g i (Fin.last n)) (-t))
      (fun k => (g i k.castSucc : K → ℂ)) j
  have hT : ((partialFourierEquiv ψ ν n hsd (entryProductTest g) :
      SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
        Matrix (Fin n) (Fin (n + 1)) K → ℂ) =
      fun a => ∏ i, ∏ j, g' i j (a i j) := by
    funext a
    rw [partialFourierEquiv_apply]
    change partialFourierIntegral ψ ν (fun X => ∏ i, ∏ j, (g i j : K → ℂ) (X i j)) a = _
    rw [partialFourierIntegral_entryProduct]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [g', Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [rectangularFourierEquiv_apply, hT, rectangularFourierIntegral_entryProduct,
    rectangularFixedLastColumn_entryProduct, map_smul]
  change _ = (∏ i, g i (Fin.last n) (b i)) *
    rectangularFourierEquiv ψ ν n n hsd (entryProductTest (fun i j => g i j.castSucc)) A
  rw [rectangularFourierEquiv_apply]
  change _ = (∏ i, g i (Fin.last n) (b i)) *
    rectangularFourierIntegral ψ ν (fun X => ∏ i, ∏ j, (g i j.castSucc : K → ℂ) (X i j)) A
  rw [rectangularFourierIntegral_entryProduct]
  simp only [Fin.prod_univ_castSucc, g', Fin.lastCases_castSucc, Fin.lastCases_last,
    rectangularJoin_castSucc, rectangularJoin_last]
  have hinv (i : Fin n) :
      fourierIntegral ψ ν (fun t => fourierIntegral ψ ν (g i (Fin.last n)) (-t)) (b i) =
        g i (Fin.last n) (b i) := by
    rw [fourierIntegral_comp_neg]
    have hi := (hsd (g i (Fin.last n))).2 (-b i)
    change fourierIntegral ψ ν (fourierIntegral ψ ν (g i (Fin.last n))) (-b i) =
      g i (Fin.last n) (-(-b i)) at hi
    simpa only [neg_neg] using hi
  simp only [hinv, Finset.prod_mul_distrib]
  exact mul_comm _ _

/-- Full plus Fourier after inverse-character final-column Fourier is precisely
square plus Fourier of the original fixed-column slice. -/
theorem rectangularFourierEquiv_partial_fixedLastColumn
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K) :
    rectangularFourierEquiv ψ ν n (n + 1) hsd
        (partialFourierEquiv ψ ν n hsd Φ) (rectangularJoin A b) =
      rectangularFourierEquiv ψ ν n n hsd (rectangularFixedLastColumn b Φ) A := by
  obtain ⟨M, c, g, hΦ⟩ := matrixTensorDecomposition Φ
  have hsum : Φ = ∑ k, c k • entryProductTest (g k) := by
    ext X
    rw [hΦ X]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, entryProductTest_apply]
  rw [hsum]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ =>
    congrArg (c k * ·) (full_partial_entryProduct ψ ν hsd (g k) A b)

end Langlands.HarmonicAnalysis
