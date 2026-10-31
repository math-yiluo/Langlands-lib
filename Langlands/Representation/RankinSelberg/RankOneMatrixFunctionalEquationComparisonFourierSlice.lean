import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof

/-! Coordinate slicing of the actual plus Fourier integral. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [T2Space K]

/-- The coordinates in `S` carry the supplied scalar Haar measure; the other
coordinates are fixed at `c`. This is an actual product measure. -/
def coordinateSliceMeasure (ν : AdditiveHaarMeasure K) {d : ℕ}
    (S : Finset (Fin d)) (c : Fin d → K) : Measure (Fin d → K) :=
  Measure.pi (fun i => if i ∈ S then ν.measure else Measure.dirac (c i))

/-- A vector supported in the selected coordinates. -/
def coordinateMask {d : ℕ} (S : Finset (Fin d)) (a : Fin d → K) : Fin d → K :=
  fun i => if i ∈ S then a i else 0

private instance sliceCoordinate_sigmaFinite (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] {d : ℕ} (S : Finset (Fin d)) (c : Fin d → K) (i : Fin d) :
    SigmaFinite (if i ∈ S then ν.measure else Measure.dirac (c i)) := by
  split_ifs <;> infer_instance

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] [T2Space K] in
private theorem character_sum (ψ : UnitaryAdditiveCharacter K) {ι : Type*}
    (S : Finset ι) (a : ι → K) :
    ψ.complex (∑ i ∈ S, a i) = ∏ i ∈ S, ψ.complex (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] [T2Space K] in
private theorem tensor_kernel (ψ : UnitaryAdditiveCharacter K) {d : ℕ}
    (g : Fin d → K → ℂ) (b x : Fin d → K) :
    ψ.complex (rowPairing x b) * ∏ i, g i (x i) =
      ∏ i, ψ.complex (x i * b i) * g i (x i) := by
  rw [rowPairing, character_sum]
  exact Finset.prod_mul_distrib.symm

omit [IsTopologicalRing K] in
/-- Integration on a coordinate slice retains precisely the free-coordinate
scalar integrals and the fixed-coordinate evaluations. -/
theorem coordinateSlice_integral_tensor (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] {d : ℕ}
    (S : Finset (Fin d)) (c b : Fin d → K) (g : Fin d → K → ℂ) :
    (∫ x, ψ.complex (rowPairing x b) * ∏ i, g i (x i)
      ∂coordinateSliceMeasure ν S c) =
      ∏ i, if i ∈ S then fourierIntegral ψ ν (g i) (b i)
        else ψ.complex (c i * b i) * g i (c i) := by
  simp_rw [tensor_kernel]
  unfold coordinateSliceMeasure
  rw [integral_fintype_prod_eq_prod
    (μ := fun i : Fin d => if i ∈ S then ν.measure else Measure.dirac (c i))
    (fun i x => ψ.complex (x * b i) * g i x)]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · exact integral_dirac _ _

omit [IsTopologicalRing K] in
private theorem coordinateSlice_integrable_tensor (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] {d : ℕ}
    (S : Finset (Fin d)) (c b : Fin d → K) (g : Fin d → K → ℂ)
    (hg : ∀ i ∈ S, Integrable (fun x => ψ.complex (x * b i) * g i x) ν.measure) :
    Integrable (fun x => ψ.complex (rowPairing x b) * ∏ i, g i (x i))
      (coordinateSliceMeasure ν S c) := by
  simp_rw [tensor_kernel]
  unfold coordinateSliceMeasure
  apply Integrable.fintype_prod
    (μ := fun i : Fin d => if i ∈ S then ν.measure else Measure.dirac (c i))
    (f := fun i x => ψ.complex (x * b i) * g i x)
  intro i
  split_ifs with hi
  · exact hg i hi
  · exact integrable_dirac (by simp)

omit [IsTopologicalRing K] [BorelSpace K] [T2Space K] in
private theorem rowFourierIntegral_tensor (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] {d : ℕ}
    (g : Fin d → K → ℂ) (y : Fin d → K) :
    rowFourierIntegral ψ ν d (fun x => ∏ i, g i (x i)) y =
      ∏ i, fourierIntegral ψ ν (g i) (y i) := by
  unfold rowFourierIntegral rowMeasure fourierIntegral
  simp_rw [tensor_kernel]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin d => ν.measure)
    (fun i x => ψ.complex (x * y i) * g i x)

omit [T2Space K] in
private theorem rowFourierIntegral_decomposition (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] {d N : ℕ}
    (Φ : SchwartzBruhat (Fin d → K)) (c : Fin N → ℂ)
    (g : Fin N → Fin d → SchwartzBruhat K)
    (hf : ∀ x, Φ x = ∑ j, c j * ∏ i, g j i (x i)) (y : Fin d → K) :
    rowFourierIntegral ψ ν d Φ y =
      ∑ j, c j * ∏ i, fourierIntegral ψ ν (g j i) (y i) := by
  have hi (j : Fin N) : Integrable
      (fun x : Fin d → K => ψ.complex (rowPairing x y) * ∏ i, g j i (x i))
      (rowMeasure ν d) := by
    simp_rw [tensor_kernel]
    exact Integrable.fintype_prod (fun i => fourierIntegrand_integrable ψ ν (g j i) (y i))
  unfold rowFourierIntegral
  simp_rw [hf, Finset.mul_sum, mul_left_comm _ (c _)]
  rw [integral_finsetSum Finset.univ (fun j _ => (hi j).const_mul (c j))]
  simp_rw [integral_const_mul]
  exact Finset.sum_congr rfl fun j _ =>
    congrArg (c j * ·) (rowFourierIntegral_tensor ψ ν (fun i => g j i) y)

section SelfDual

variable [LocallyCompactSpace K] [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
  [SigmaFinite ν.measure]

private theorem coordinateSlice_tensor_duality (hsd : IsSelfDual ψ ν)
    {d : ℕ} (S : Finset (Fin d))
    (a b : Fin d → K) (g : Fin d → SchwartzBruhat K) :
    (∫ y, ψ.complex (rowPairing y (coordinateMask S (-a))) *
        ∏ i, fourierIntegral ψ ν (g i) (y i)
      ∂coordinateSliceMeasure ν S b) =
      ∫ x, ψ.complex (rowPairing x (coordinateMask Sᶜ b)) * ∏ i, g i (x i)
        ∂coordinateSliceMeasure ν Sᶜ a := by
  rw [coordinateSlice_integral_tensor, coordinateSlice_integral_tensor]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp only [coordinateMask, hi, Finset.mem_compl, not_true_eq_false,
      ite_true, ite_false, Pi.neg_apply, mul_zero, AddChar.map_zero_eq_one, one_mul]
    exact (hsd (g i)).2 (-a i) |>.trans (congrArg (g i) (neg_neg _))
  · simp only [coordinateMask, hi, Finset.mem_compl, not_false_eq_true,
      ite_true, ite_false, mul_zero, AddChar.map_zero_eq_one, one_mul]

/-- Partial Fourier inversion on complementary affine coordinate slices.
Both integrals converge absolutely. The negative phase on the transformed
side fixes the original free coordinates at `a`; the original-side phase is
the value `b` of the transformed fixed coordinates. -/
theorem coordinateSlice_fourier_duality (hsd : IsSelfDual ψ ν)
    {d : ℕ} (Φ : SchwartzBruhat (Fin d → K))
    (S : Finset (Fin d)) (a b : Fin d → K) :
    Integrable (fun y => ψ.complex (rowPairing y (coordinateMask S (-a))) *
        rowFourierIntegral ψ ν d Φ y) (coordinateSliceMeasure ν S b) ∧
    Integrable (fun x => ψ.complex (rowPairing x (coordinateMask Sᶜ b)) * Φ x)
      (coordinateSliceMeasure ν Sᶜ a) ∧
    (∫ y, ψ.complex (rowPairing y (coordinateMask S (-a))) *
        rowFourierIntegral ψ ν d Φ y ∂coordinateSliceMeasure ν S b) =
      ∫ x, ψ.complex (rowPairing x (coordinateMask Sᶜ b)) * Φ x
        ∂coordinateSliceMeasure ν Sᶜ a := by
  classical
  obtain ⟨N, c, g, hf⟩ := rowTensorDecomposition K d Φ
  have hhat := rowFourierIntegral_decomposition ψ ν Φ c g hf
  have hleft (j : Fin N) : Integrable
      (fun y => ψ.complex (rowPairing y (coordinateMask S (-a))) *
        ∏ i, fourierIntegral ψ ν (g j i) (y i)) (coordinateSliceMeasure ν S b) := by
    apply coordinateSlice_integrable_tensor
    intro i hi
    have ht := (hsd (g j i)).1 (-a i)
    change Integrable (fun x : K => ψ.complex (x * -a i) *
      fourierIntegral ψ ν (g j i) x) ν.measure at ht
    simpa only [coordinateMask, hi, ite_true, Pi.neg_apply] using ht
  have hright (j : Fin N) : Integrable
      (fun x => ψ.complex (rowPairing x (coordinateMask Sᶜ b)) *
        ∏ i, g j i (x i)) (coordinateSliceMeasure ν Sᶜ a) := by
    apply coordinateSlice_integrable_tensor
    intro i _
    exact fourierIntegrand_integrable ψ ν (g j i) _
  have hl : Integrable
      (fun y => ∑ j, c j * (ψ.complex (rowPairing y (coordinateMask S (-a))) *
        ∏ i, fourierIntegral ψ ν (g j i) (y i))) (coordinateSliceMeasure ν S b) :=
    integrable_finsetSum Finset.univ fun j _ => (hleft j).const_mul (c j)
  have hr : Integrable
      (fun x => ∑ j, c j * (ψ.complex (rowPairing x (coordinateMask Sᶜ b)) *
        ∏ i, g j i (x i))) (coordinateSliceMeasure ν Sᶜ a) :=
    integrable_finsetSum Finset.univ fun j _ => (hright j).const_mul (c j)
  have eleft : (fun y => ψ.complex (rowPairing y (coordinateMask S (-a))) *
        rowFourierIntegral ψ ν d Φ y) =
      fun y => ∑ j, c j * (ψ.complex (rowPairing y (coordinateMask S (-a))) *
        ∏ i, fourierIntegral ψ ν (g j i) (y i)) := by
    funext y
    rw [hhat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _
  have eright : (fun x => ψ.complex (rowPairing x (coordinateMask Sᶜ b)) * Φ x) =
      fun x => ∑ j, c j * (ψ.complex (rowPairing x (coordinateMask Sᶜ b)) *
        ∏ i, g j i (x i)) := by
    funext x
    rw [hf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _
  refine ⟨eleft ▸ hl, eright ▸ hr, ?_⟩
  rw [eleft, eright, integral_finsetSum Finset.univ (fun j _ => (hleft j).const_mul (c j)),
    integral_finsetSum Finset.univ (fun j _ => (hright j).const_mul (c j))]
  simp_rw [integral_const_mul]
  exact Finset.sum_congr rfl fun j _ =>
    congrArg (c j * ·) (coordinateSlice_tensor_duality ψ ν hsd S a b (g j))

end SelfDual

end Langlands.HarmonicAnalysis
