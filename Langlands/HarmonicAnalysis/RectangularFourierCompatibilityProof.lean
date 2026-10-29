import Langlands.HarmonicAnalysis.RectangularFourierCompatibilityStatement
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

private def productTest {X : Type uK} [TopologicalSpace X] [T2Space X]
    {d : ℕ} (g : Fin d → SchwartzBruhat X) : SchwartzBruhat (Fin d → X) := by
  refine ⟨fun x => ∏ i, g i (x i), ?_, ?_⟩
  · have hl (S : Finset (Fin d)) : IsLocallyConstant
        (fun x : Fin d → X => ∏ i ∈ S, g i (x i)) := by
      induction S using Finset.induction_on with
      | empty =>
        simpa only [Finset.prod_empty, Function.const_def] using
          (IsLocallyConstant.const (1 : ℂ) (X := Fin d → X))
      | @insert i S hi ih =>
        simpa only [Finset.prod_insert hi, Function.comp_def] using
          ((g i).locallyConstant.comp_continuous (continuous_apply i)).comp₂ ih (· * ·)
    exact hl Finset.univ
  · apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_univ_pi fun i => (g i).hasCompactSupport)
    intro x hx
    simp only [Set.mem_univ_pi]
    intro i
    apply subset_tsupport (g i)
    change g i (x i) ≠ 0
    intro hi
    exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hi)

section ScalarAndRows

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
private theorem character_sum {ι : Type*} (ψ : UnitaryAdditiveCharacter K)
    (S : Finset ι) (a : ι → K) :
    ψ.complex (∑ i ∈ S, a i) = ∏ i ∈ S, ψ.complex (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
private theorem scalarTensor_kernel (ψ : UnitaryAdditiveCharacter K) {d : ℕ}
    (g : Fin d → K → ℂ) (x y : Fin d → K) :
    ψ.complex (rowPairing x y) * ∏ i, g i (x i) =
      ∏ i, ψ.complex (x i * y i) * g i (x i) := by
  rw [rowPairing, character_sum]
  exact Finset.prod_mul_distrib.symm

private theorem rowIntegrable [LocallyCompactSpace K] [T2Space K]
    [TotallyDisconnectedSpace K] (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure] {s : ℕ}
    (f : SchwartzBruhat (Fin s → K)) (b : Fin s → K) :
    Integrable (fun a => ψ.complex (rowPairing a b) * f a) (rowMeasure μ s) := by
  classical
  obtain ⟨N, c, g, hf⟩ := rowTensorDecomposition K s f
  have ht (j : Fin N) : Integrable
      (fun a : Fin s → K => ψ.complex (rowPairing a b) * ∏ i, g j i (a i))
      (rowMeasure μ s) := by
    simp_rw [scalarTensor_kernel]
    exact Integrable.fintype_prod (fun i => fourierIntegrand_integrable ψ μ (g j i) (b i))
  have hs := integrable_finsetSum Finset.univ (fun j _ => (ht j).const_mul (c j))
  convert hs using 1
  funext a
  rw [hf a, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

end ScalarAndRows

section Matrices

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
  [SigmaFinite μ.measure] {r s : ℕ}

private def matrixTest (g : Fin r → SchwartzBruhat (Fin s → K)) :
    SchwartzBruhat (Matrix (Fin r) (Fin s) K) := productTest g

omit [Field K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [TotallyDisconnectedSpace K] in
@[simp] private theorem matrixTest_apply (g : Fin r → SchwartzBruhat (Fin s → K))
    (a : Matrix (Fin r) (Fin s) K) : matrixTest g a = ∏ i, g i (a i) := rfl

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K] in
private theorem rowTensor_kernel (g : Fin r → (Fin s → K) → ℂ)
    (a b : Matrix (Fin r) (Fin s) K) :
    (∏ i, g i (a i)) * ψ.complex (rectangularPairing a b) =
      ∏ i, ψ.complex (rowPairing (a i) (b i)) * g i (a i) := by
  rw [mul_comm, rectangularPairing, character_sum]
  exact Finset.prod_mul_distrib.symm

omit [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K] in
private theorem rectangularTensor_integral (g : Fin r → (Fin s → K) → ℂ)
    (b : Matrix (Fin r) (Fin s) K) :
    rectangularFourierIntegral ψ μ (fun a => ∏ i, g i (a i)) b =
      ∏ i, rowFourierIntegral ψ μ s (g i) (b i) := by
  unfold rectangularFourierIntegral RankinSelberg.rectangularMeasure rowFourierIntegral rowMeasure
  simp_rw [rowTensor_kernel]
  exact integral_fintype_prod_eq_prod
    (μ := fun _ : Fin r => rowMeasure μ s)
    (fun i a => ψ.complex (rowPairing a (b i)) * g i a)

private theorem rectangularIntegrable
    (f : SchwartzBruhat (Matrix (Fin r) (Fin s) K))
    (b : Matrix (Fin r) (Fin s) K) :
    Integrable (fun a => f a * ψ.complex (rectangularPairing a b))
      (RankinSelberg.rectangularMeasure μ r s) := by
  classical
  obtain ⟨N, c, g, hf⟩ := rowTensorDecomposition (Fin s → K) r f
  have ht (j : Fin N) : Integrable
      (fun a : Matrix (Fin r) (Fin s) K =>
        (∏ i, g j i (a i)) * ψ.complex (rectangularPairing a b))
      (RankinSelberg.rectangularMeasure μ r s) := by
    simp_rw [rowTensor_kernel]
    exact Integrable.fintype_prod (fun i => rowIntegrable ψ μ (g j i) (b i))
  have hs := integrable_finsetSum Finset.univ (fun j _ => (ht j).const_mul (c j))
  convert hs using 1
  funext a
  rw [hf a, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

private theorem rectangularIntegral_sum {N : ℕ} (c : Fin N → ℂ)
    (g : Fin N → SchwartzBruhat (Matrix (Fin r) (Fin s) K))
    (b : Matrix (Fin r) (Fin s) K) :
    rectangularFourierIntegral ψ μ
      (∑ j, c j • g j : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) b =
      ∑ j, c j * rectangularFourierIntegral ψ μ (g j) b := by
  classical
  unfold rectangularFourierIntegral
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  simp_rw [mul_assoc]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => integral_const_mul (c j) _
  · intro j _
    exact (rectangularIntegrable ψ μ (g j) b).const_mul (c j)

private theorem rectangularPartner
    (hrow : RowFourierClosed ψ μ s ∧ IsRowSelfDual ψ μ s)
    (f : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) :
    ∃ k : SchwartzBruhat (Matrix (Fin r) (Fin s) K),
      (∀ b, k b = rectangularFourierIntegral ψ μ f b) ∧
      ∀ b, rectangularFourierIntegral ψ μ k b = f (-b) := by
  classical
  obtain ⟨N, c, g, hf⟩ := rowTensorDecomposition (Fin s → K) r f
  choose ghat hghat using fun j i => hrow.1 (g j i)
  have hf' : f = ∑ j, c j • matrixTest (g j) := by
    apply Hecke.TestFunction.ext
    intro a
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, matrixTest_apply] using hf a
  let k : SchwartzBruhat (Matrix (Fin r) (Fin s) K) :=
    ∑ j, c j • matrixTest (ghat j)
  refine ⟨k, ?_, ?_⟩
  · intro b
    rw [hf', rectangularIntegral_sum ψ μ]
    change (∑ j, c j • matrixTest (ghat j) :
      SchwartzBruhat (Matrix (Fin r) (Fin s) K)) b = _
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    change (∏ i, ghat j i (b i)) =
      rectangularFourierIntegral ψ μ (fun a => ∏ i, g j i (a i)) b
    rw [rectangularTensor_integral]
    exact Finset.prod_congr rfl fun i _ => hghat j i (b i)
  · intro b
    change rectangularFourierIntegral ψ μ
      (∑ j, c j • matrixTest (ghat j) :
        SchwartzBruhat (Matrix (Fin r) (Fin s) K)) b = _
    rw [rectangularIntegral_sum ψ μ, hf (-b)]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    change rectangularFourierIntegral ψ μ (fun a => ∏ i, ghat j i (a i)) b = _
    rw [rectangularTensor_integral]
    apply Finset.prod_congr rfl
    intro i _
    have hi : (ghat j i : (Fin s → K) → ℂ) =
        rowFourierIntegral ψ μ s (g j i) :=
      funext (hghat j i)
    rw [hi]
    exact (hrow.2 (g j i)).2 (b i)

end Matrices

/-- Scalar self-duality gives the full rectangular Schwartz Fourier equivalence,
its reflected inverse, square-reflection, and convergence on the supplied measure. -/
theorem rectangularFourierCompatibility :
    RectangularFourierCompatibilityStatement.{uK} := by
  classical
  intro K _ _ _ _ _ _ _ _ ψ μ r s hsd
  obtain ⟨hσ, _⟩ := scalarFourierClosure K ψ μ hsd
  let : SigmaFinite μ.measure := hσ
  have hrow := rowFourierCompatibility ψ μ s hsd
  choose F hF hF2 using
    (rectangularPartner (r := r) (s := s) ψ μ hrow)
  let L : SchwartzBruhat (Matrix (Fin r) (Fin s) K) →ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin r) (Fin s) K) :=
    { toFun := F
      map_add' := by
        intro f g
        apply Hecke.TestFunction.ext
        intro b
        change F (f + g) b = F f b + F g b
        rw [hF, hF, hF]
        unfold rectangularFourierIntegral
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact integral_add (rectangularIntegrable ψ μ f b)
          (rectangularIntegrable ψ μ g b)
      map_smul' := by
        intro c f
        apply Hecke.TestFunction.ext
        intro b
        change F (c • f) b = c * F f b
        rw [hF, hF]
        unfold rectangularFourierIntegral
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul c _ }
  have hL (f : SchwartzBruhat (Matrix (Fin r) (Fin s) K))
      (b : Matrix (Fin r) (Fin s) K) : L (L f) b = f (-b) :=
    (hF (F f) b).trans (hF2 f b)
  have hbij : Function.Bijective L := by
    constructor
    · intro f g hfg
      apply Hecke.TestFunction.ext
      intro b
      calc
        f b = L (L f) (-b) := by simpa only [neg_neg] using (hL f (-b)).symm
        _ = L (L g) (-b) := by rw [hfg]
        _ = g b := by simpa only [neg_neg] using hL g (-b)
    · intro f
      let fneg := Hecke.TestFunction.pullback
        (Homeomorph.neg (Matrix (Fin r) (Fin s) K)) f
      refine ⟨L fneg, ?_⟩
      apply Hecke.TestFunction.ext
      intro b
      rw [hL]
      change f (-(-b)) = f b
      rw [neg_neg]
  let T := LinearEquiv.ofBijective L hbij
  refine ⟨T, hF, ?_, hL, rectangularIntegrable ψ μ⟩
  intro f b
  calc
    T.symm f b = T f (-b) := by
      have h := hL (T.symm f) (-b)
      change T (T (T.symm f)) (-b) = T.symm f (-(-b)) at h
      simpa only [LinearEquiv.apply_symm_apply, neg_neg] using h.symm
    _ = rectangularFourierIntegral ψ μ f (-b) := hF f (-b)

end Langlands.HarmonicAnalysis
