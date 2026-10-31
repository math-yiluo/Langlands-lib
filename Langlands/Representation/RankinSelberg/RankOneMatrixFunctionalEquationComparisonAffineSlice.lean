import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierSlice
import Langlands.HarmonicAnalysis.RectangularFourier

/-! Actual partial Fourier inversion on complementary affine matrix slices. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [T2Space K]

/-- A nested product measure with the supplied scalar Haar on the selected
entries and Dirac masses on the other entries. -/
def rectangularCoordinateSliceMeasure (ν : AdditiveHaarMeasure K) {r s : ℕ}
    (S : Fin r → Finset (Fin s)) (c : Matrix (Fin r) (Fin s) K) :
    Measure (Matrix (Fin r) (Fin s) K) :=
  Measure.pi (fun i => coordinateSliceMeasure ν (S i) (c i))

/-- Entrywise coordinate masking, with a separate selected set in each row. -/
def rectangularCoordinateMask {r s : ℕ} (S : Fin r → Finset (Fin s))
    (a : Matrix (Fin r) (Fin s) K) : Matrix (Fin r) (Fin s) K :=
  fun i => coordinateMask (S i) (a i)

private instance sliceEntry_sigmaFinite (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] {s : ℕ} (S : Finset (Fin s)) (c : Fin s → K) (i : Fin s) :
    SigmaFinite (if i ∈ S then ν.measure else Measure.dirac (c i)) := by
  split_ifs <;> infer_instance

private instance sliceRow_sigmaFinite (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] {s : ℕ} (S : Finset (Fin s)) (c : Fin s → K) :
    SigmaFinite (coordinateSliceMeasure ν S c) := by
  unfold coordinateSliceMeasure
  infer_instance

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] [T2Space K] in
private theorem character_sum (ψ : UnitaryAdditiveCharacter K) {ι : Type*}
    (S : Finset ι) (a : ι → K) :
    ψ.complex (∑ i ∈ S, a i) = ∏ i ∈ S, ψ.complex (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] [T2Space K] in
private theorem matrixTensor_kernel (ψ : UnitaryAdditiveCharacter K) {r s : ℕ}
    (g : Fin r → (Fin s → K) → ℂ) (b x : Matrix (Fin r) (Fin s) K) :
    ψ.complex (rectangularPairing x b) * ∏ i, g i (x i) =
      ∏ i, ψ.complex (rowPairing (x i) (b i)) * g i (x i) := by
  change ψ.complex (∑ i, rowPairing (x i) (b i)) * _ = _
  rw [character_sum]
  exact Finset.prod_mul_distrib.symm

omit [IsTopologicalRing K] [BorelSpace K] [T2Space K] in
private theorem rectangularSlice_integral_tensor (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] {r s : ℕ}
    (S : Fin r → Finset (Fin s)) (c b : Matrix (Fin r) (Fin s) K)
    (g : Fin r → (Fin s → K) → ℂ) :
    (∫ x, ψ.complex (rectangularPairing x b) * ∏ i, g i (x i)
      ∂rectangularCoordinateSliceMeasure ν S c) =
      ∏ i, ∫ z, ψ.complex (rowPairing z (b i)) * g i z
        ∂coordinateSliceMeasure ν (S i) (c i) := by
  let : ∀ i : Fin r, SigmaFinite (coordinateSliceMeasure ν (S i) (c i)) :=
    fun i => sliceRow_sigmaFinite ν (S i) (c i)
  simp_rw [matrixTensor_kernel]
  unfold rectangularCoordinateSliceMeasure
  exact integral_fintype_prod_eq_prod
    (μ := fun i : Fin r => coordinateSliceMeasure ν (S i) (c i))
    (fun i z => ψ.complex (rowPairing z (b i)) * g i z)

omit [IsTopologicalRing K] [BorelSpace K] [T2Space K] in
private theorem rectangularSlice_integrable_tensor (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] {r s : ℕ}
    (S : Fin r → Finset (Fin s)) (c b : Matrix (Fin r) (Fin s) K)
    (g : Fin r → (Fin s → K) → ℂ)
    (hg : ∀ i, Integrable (fun z => ψ.complex (rowPairing z (b i)) * g i z)
      (coordinateSliceMeasure ν (S i) (c i))) :
    Integrable (fun x => ψ.complex (rectangularPairing x b) * ∏ i, g i (x i))
      (rectangularCoordinateSliceMeasure ν S c) := by
  let : ∀ i : Fin r, SigmaFinite (coordinateSliceMeasure ν (S i) (c i)) :=
    fun i => sliceRow_sigmaFinite ν (S i) (c i)
  simp_rw [matrixTensor_kernel]
  unfold rectangularCoordinateSliceMeasure
  exact Integrable.fintype_prod
    (μ := fun i : Fin r => coordinateSliceMeasure ν (S i) (c i))
    (f := fun i z => ψ.complex (rowPairing z (b i)) * g i z) hg

omit [IsTopologicalRing K] [BorelSpace K] [T2Space K] in
private theorem rectangularFourierIntegral_tensor (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] {r s : ℕ}
    (g : Fin r → (Fin s → K) → ℂ) (y : Matrix (Fin r) (Fin s) K) :
    rectangularFourierIntegral ψ ν (fun x => ∏ i, g i (x i)) y =
      ∏ i, rowFourierIntegral ψ ν s (g i) (y i) := by
  unfold rectangularFourierIntegral RankinSelberg.rectangularMeasure rowFourierIntegral
  simp_rw [mul_comm (∏ _, _) (ψ.complex _), matrixTensor_kernel]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin r => rowMeasure ν s)
    (fun i z => ψ.complex (rowPairing z (y i)) * g i z)

section SelfDual

variable [LocallyCompactSpace K] [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
  [SigmaFinite ν.measure]

private theorem rectangularFourierIntegral_decomposition (hsd : IsSelfDual ψ ν)
    {r s N : ℕ}
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) (c : Fin N → ℂ)
    (g : Fin N → Fin r → SchwartzBruhat (Fin s → K))
    (hf : ∀ x, Φ x = ∑ j, c j * ∏ i, g j i (x i))
    (y : Matrix (Fin r) (Fin s) K) :
    rectangularFourierIntegral ψ ν Φ y =
      ∑ j, c j * ∏ i, rowFourierIntegral ψ ν s (g j i) (y i) := by
  have hi (j : Fin N) : Integrable
      (fun x : Matrix (Fin r) (Fin s) K =>
        ψ.complex (rectangularPairing x y) * ∏ i, g j i (x i))
      (RankinSelberg.rectangularMeasure ν r s) := by
    simp_rw [matrixTensor_kernel]
    exact Integrable.fintype_prod (μ := fun _ : Fin r => rowMeasure ν s)
      (f := fun i z => ψ.complex (rowPairing z (y i)) * g j i z)
      (fun i => by
        have hrow := (coordinateSlice_fourier_duality ψ ν hsd (g j i)
          ∅ 0 (y i)).2.1
        have hm : coordinateMask (Finset.univ : Finset (Fin s)) (y i) = y i := by
          funext k
          simp [coordinateMask]
        simpa only [Finset.compl_empty, hm, coordinateSliceMeasure,
          Finset.mem_univ, ite_true, rowMeasure] using hrow)
  have he : (fun x : Matrix (Fin r) (Fin s) K =>
        Φ x * ψ.complex (rectangularPairing x y)) =
      fun x => ∑ j, c j *
        (ψ.complex (rectangularPairing x y) * ∏ i, g j i (x i)) := by
    funext x
    rw [hf x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold rectangularFourierIntegral
  rw [he, integral_finsetSum Finset.univ (fun j _ => (hi j).const_mul (c j))]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (c j * ·)
  calc
    _ = rectangularFourierIntegral ψ ν (fun x => ∏ i, g j i (x i)) y :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    _ = _ := rectangularFourierIntegral_tensor ψ ν (fun i => g j i) y

private theorem rectangularSlice_tensor_duality (hsd : IsSelfDual ψ ν) {r s : ℕ}
    (S : Fin r → Finset (Fin s)) (a b : Matrix (Fin r) (Fin s) K)
    (g : Fin r → SchwartzBruhat (Fin s → K)) :
    (∫ y, ψ.complex (rectangularPairing y (rectangularCoordinateMask S (-a))) *
        ∏ i, rowFourierIntegral ψ ν s (g i) (y i)
      ∂rectangularCoordinateSliceMeasure ν S b) =
      ∫ x, ψ.complex (rectangularPairing x
        (rectangularCoordinateMask (fun i => (S i)ᶜ) b)) * ∏ i, g i (x i)
        ∂rectangularCoordinateSliceMeasure ν (fun i => (S i)ᶜ) a := by
  rw [rectangularSlice_integral_tensor, rectangularSlice_integral_tensor]
  exact Finset.prod_congr rfl fun i _ =>
    (coordinateSlice_fourier_duality ψ ν hsd (g i) (S i) (a i) (b i)).2.2

/-- Partial Fourier inversion on the actual complementary affine matrix slices,
including absolute convergence on both sides and zero rectangular dimensions. -/
theorem rectangularCoordinateSlice_fourier_duality (hsd : IsSelfDual ψ ν) {r s : ℕ}
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K))
    (S : Fin r → Finset (Fin s)) (a b : Matrix (Fin r) (Fin s) K) :
    Integrable (fun y => ψ.complex (rectangularPairing y
      (rectangularCoordinateMask S (-a))) * rectangularFourierIntegral ψ ν Φ y)
      (rectangularCoordinateSliceMeasure ν S b) ∧
    Integrable (fun x => ψ.complex (rectangularPairing x
      (rectangularCoordinateMask (fun i => (S i)ᶜ) b)) * Φ x)
      (rectangularCoordinateSliceMeasure ν (fun i => (S i)ᶜ) a) ∧
    (∫ y, ψ.complex (rectangularPairing y (rectangularCoordinateMask S (-a))) *
      rectangularFourierIntegral ψ ν Φ y ∂rectangularCoordinateSliceMeasure ν S b) =
      ∫ x, ψ.complex (rectangularPairing x
        (rectangularCoordinateMask (fun i => (S i)ᶜ) b)) * Φ x
        ∂rectangularCoordinateSliceMeasure ν (fun i => (S i)ᶜ) a := by
  classical
  obtain ⟨N, c, g, hf⟩ := rowTensorDecomposition (Fin s → K) r Φ
  have hhat := rectangularFourierIntegral_decomposition ψ ν hsd Φ c g hf
  have hleft (j : Fin N) : Integrable
      (fun y => ψ.complex (rectangularPairing y (rectangularCoordinateMask S (-a))) *
        ∏ i, rowFourierIntegral ψ ν s (g j i) (y i))
      (rectangularCoordinateSliceMeasure ν S b) := by
    apply rectangularSlice_integrable_tensor
    exact fun i => (coordinateSlice_fourier_duality ψ ν hsd (g j i) (S i) (a i) (b i)).1
  have hright (j : Fin N) : Integrable
      (fun x => ψ.complex (rectangularPairing x
        (rectangularCoordinateMask (fun i => (S i)ᶜ) b)) * ∏ i, g j i (x i))
      (rectangularCoordinateSliceMeasure ν (fun i => (S i)ᶜ) a) := by
    apply rectangularSlice_integrable_tensor
    exact fun i => (coordinateSlice_fourier_duality ψ ν hsd (g j i) (S i) (a i) (b i)).2.1
  have hl : Integrable (fun y => ∑ j, c j *
      (ψ.complex (rectangularPairing y (rectangularCoordinateMask S (-a))) *
        ∏ i, rowFourierIntegral ψ ν s (g j i) (y i)))
      (rectangularCoordinateSliceMeasure ν S b) :=
    integrable_finsetSum Finset.univ fun j _ => (hleft j).const_mul (c j)
  have hr : Integrable (fun x => ∑ j, c j *
      (ψ.complex (rectangularPairing x
        (rectangularCoordinateMask (fun i => (S i)ᶜ) b)) * ∏ i, g j i (x i)))
      (rectangularCoordinateSliceMeasure ν (fun i => (S i)ᶜ) a) :=
    integrable_finsetSum Finset.univ fun j _ => (hright j).const_mul (c j)
  have eleft : (fun y => ψ.complex (rectangularPairing y
        (rectangularCoordinateMask S (-a))) * rectangularFourierIntegral ψ ν Φ y) =
      fun y => ∑ j, c j * (ψ.complex (rectangularPairing y
        (rectangularCoordinateMask S (-a))) *
        ∏ i, rowFourierIntegral ψ ν s (g j i) (y i)) := by
    funext y
    rw [hhat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _
  have eright : (fun x => ψ.complex (rectangularPairing x
        (rectangularCoordinateMask (fun i => (S i)ᶜ) b)) * Φ x) =
      fun x => ∑ j, c j * (ψ.complex (rectangularPairing x
        (rectangularCoordinateMask (fun i => (S i)ᶜ) b)) * ∏ i, g j i (x i)) := by
    funext x
    rw [hf x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _
  refine ⟨eleft ▸ hl, eright ▸ hr, ?_⟩
  rw [eleft, eright, integral_finsetSum Finset.univ (fun j _ => (hleft j).const_mul (c j)),
    integral_finsetSum Finset.univ (fun j _ => (hright j).const_mul (c j))]
  simp_rw [integral_const_mul]
  exact Finset.sum_congr rfl fun j _ => congrArg (c j * ·)
    (rectangularSlice_tensor_duality ψ ν hsd S a b (g j))

end SelfDual

end Langlands.HarmonicAnalysis
