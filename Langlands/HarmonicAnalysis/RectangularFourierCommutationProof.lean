import Langlands.HarmonicAnalysis.RectangularFourierCommutationStatement
import Langlands.HarmonicAnalysis.TwoBlockPartialFourier

/-!
# Commutation of the chosen full and partial rectangular Fourier transforms

Both chosen maps send an entrywise product of scalar test functions to an entrywise
product of explicit scalar functions. On such products the two composites agree by
negation invariance of the regular additive Haar measure; finite tensor decomposition
and linearity give the general case. See the paired Markdown.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

section Scalar

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)

/-- The plus-sign scalar Fourier integral of a reflected function is the reflected
Fourier integral, by negation invariance of the regular additive Haar measure. -/
theorem fourierIntegral_comp_neg (G : K → ℂ) (z : K) :
    fourierIntegral ψ μ (fun t => G (-t)) z = fourierIntegral ψ μ G (-z) := by
  unfold fourierIntegral
  rw [← integral_neg_eq_self (fun x => ψ.complex (x * z) * G (-x)) μ.measure]
  simp only [neg_neg, neg_mul, mul_neg]

end Scalar

section EntryProducts

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
  [SigmaFinite μ.measure] {n : ℕ}

omit [IsTopologicalRing K] in
/-- The inverse-character last-column integral of an entrywise product keeps the
first `n` columns and replaces each last-column factor by its scalar Fourier
integral at the negated entry. -/
theorem partialFourierIntegral_entryProduct (g : Fin n → Fin (n + 1) → K → ℂ)
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    partialFourierIntegral ψ μ (fun a => ∏ i, ∏ j, g i j (a i j)) m =
      ∏ i, ((∏ k : Fin n, g i k.castSucc (m i k.castSucc)) *
        fourierIntegral ψ μ (g i (Fin.last n)) (-m i (Fin.last n))) := by
  unfold partialFourierIntegral
  have h : ∀ u : Fin n → K,
      (∏ i, ∏ j, g i j (rectangularJoin (rectangularFirstColumns m) u i j)) *
        ψ.complex (-rowPairing (rectangularLastColumn m) u) =
      (∏ i, ∏ k : Fin n, g i k.castSucc (m i k.castSucc)) *
        ∏ i, (ψ.complex (u i * -m i (Fin.last n)) * g i (Fin.last n) (u i)) := by
    intro u
    simp only [Fin.prod_univ_castSucc, rectangularJoin_castSucc, rectangularJoin_last]
    rw [rowPairing, ← Finset.sum_neg_distrib, complex_finsetSum,
      Finset.prod_mul_distrib, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 2
    simp only [rectangularLastColumn, mul_neg, mul_comm]
  simp_rw [h]
  rw [integral_const_mul, rowMeasure,
    integral_fintype_prod_eq_prod
      (fun i (t : K) => ψ.complex (t * -m i (Fin.last n)) * g i (Fin.last n) t),
    ← Finset.prod_mul_distrib]
  rfl

end EntryProducts

section Commutation

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) {n : ℕ}
  (hsd : IsSelfDual ψ μ)

/-- The two composites agree on an entrywise product of scalar test functions. -/
theorem rectangularFourierCommutation_entryProduct
    (g : Fin n → Fin (n + 1) → SchwartzBruhat K) :
    rectangularFourierEquiv ψ μ n (n + 1) hsd
        (partialFourierEquiv ψ μ n hsd (entryProductTest g)) =
      partialFourierEquiv ψ μ n hsd
        (rectangularFourierEquiv ψ μ n (n + 1) hsd (entryProductTest g)) := by
  have : SigmaFinite μ.measure := selfDualSigmaFinite.{uK} K ψ μ hsd
  -- The partial transform of the product is again an entrywise product.
  let g' : Fin n → Fin (n + 1) → K → ℂ := fun i j =>
    Fin.lastCases (fun t => fourierIntegral ψ μ (g i (Fin.last n)) (-t))
      (fun k => (g i k.castSucc : K → ℂ)) j
  have hT : ((partialFourierEquiv ψ μ n hsd (entryProductTest g) :
      SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
        Matrix (Fin n) (Fin (n + 1)) K → ℂ) =
      fun a => ∏ i, ∏ j, g' i j (a i j) := by
    funext a
    rw [partialFourierEquiv_apply]
    have he : ((entryProductTest g : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
        Matrix (Fin n) (Fin (n + 1)) K → ℂ) = fun X => ∏ i, ∏ j, (g i j : K → ℂ) (X i j) :=
      rfl
    rw [he, partialFourierIntegral_entryProduct]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [g', Fin.lastCases_castSucc, Fin.lastCases_last]
  -- The full transform of the product is the entrywise product of scalar transforms.
  have hF : ((rectangularFourierEquiv ψ μ n (n + 1) hsd (entryProductTest g) :
      SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
        Matrix (Fin n) (Fin (n + 1)) K → ℂ) =
      fun a => ∏ i, ∏ j, fourierIntegral ψ μ (g i j) (a i j) := by
    funext a
    rw [rectangularFourierEquiv_apply]
    exact rectangularFourierIntegral_entryProduct ψ μ (fun i j => (g i j : K → ℂ)) a
  ext b
  rw [rectangularFourierEquiv_apply, partialFourierEquiv_apply, hT, hF,
    rectangularFourierIntegral_entryProduct, partialFourierIntegral_entryProduct]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp only [g', Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [fourierIntegral_comp_neg]

/-- The chosen full plus-sign rectangular Fourier equivalence commutes with the
chosen inverse-character last-column Fourier equivalence. -/
theorem rectangularFourierCommutation : RectangularFourierCommutationStatement.{uK} := by
  intro K _ _ _ _ _ _ _ _ ψ μ n hsd Φ
  obtain ⟨M, c, g, hΦ⟩ := matrixTensorDecomposition Φ
  have hsum : Φ = ∑ k, c k • entryProductTest (g k) := by
    ext X
    rw [hΦ X]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, entryProductTest_apply]
  rw [hsum]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun k _ =>
    congrArg (c k • ·) (rectangularFourierCommutation_entryProduct ψ μ hsd (g k))

end Commutation

end Langlands.HarmonicAnalysis
