import Langlands.HarmonicAnalysis.RowFourier
import Langlands.HarmonicAnalysis.ScalarFourierClosureProof
import Langlands.HarmonicAnalysis.RowTensorDecompositionProof
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe u

private def rowTensor {X : Type u} [TopologicalSpace X] [T2Space X]
    {d : ℕ} (g : Fin d → SchwartzBruhat X) : SchwartzBruhat (Fin d → X) := by
  refine ⟨fun x => ∏ i, g i (x i), ?_, ?_⟩
  · have hl (s : Finset (Fin d)) : IsLocallyConstant
        (fun x : Fin d → X => ∏ i ∈ s, g i (x i)) := by
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty, Function.const_def] using (IsLocallyConstant.const (1 : ℂ) (X := Fin d → X))
      | @insert i s hi ih =>
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

private theorem rowFourierIntegrand_tensor
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] (ψ : UnitaryAdditiveCharacter F) {d : ℕ}
    (g : Fin d → F → ℂ) (x y : Fin d → F) :
    ψ.complex (rowPairing x y) * ∏ i, g i (x i) =
      ∏ i, ψ.complex (x i * y i) * g i (x i) := by
  have hψ (s : Finset (Fin d)) :
      ψ.complex (∑ i ∈ s, x i * y i) = ∏ i ∈ s, ψ.complex (x i * y i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
        AddChar.map_add_eq_mul, ih]
  rw [rowPairing, hψ]
  exact Finset.prod_mul_distrib.symm

private theorem rowFourierIntegral_tensor
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) [SigmaFinite μ.measure] {d : ℕ}
    (g : Fin d → F → ℂ) (y : Fin d → F) :
    rowFourierIntegral ψ μ d (fun x => ∏ i, g i (x i)) y =
      ∏ i, fourierIntegral ψ μ (g i) (y i) := by
  unfold rowFourierIntegral rowMeasure fourierIntegral
  simp_rw [rowFourierIntegrand_tensor]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin d => μ.measure)
    (fun i x => ψ.complex (x * y i) * g i x)

private theorem rowFourierIntegrand_integrable_of_decomposition
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) [SigmaFinite μ.measure] {d : ℕ}
    (hdecomp : ∀ f : SchwartzBruhat (Fin d → F),
      ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Fin d → SchwartzBruhat F),
        ∀ x, f x = ∑ j, c j * ∏ i, g j i (x i))
    (f : SchwartzBruhat (Fin d → F)) (y : Fin d → F) :
    Integrable (fun x => ψ.complex (rowPairing x y) * f x) (rowMeasure μ d) := by
  classical
  obtain ⟨N, c, g, hf⟩ := hdecomp f
  have ht (j : Fin N) : Integrable
      (fun x : Fin d → F => ψ.complex (rowPairing x y) * ∏ i, g j i (x i))
      (rowMeasure μ d) := by
    simp_rw [rowFourierIntegrand_tensor]
    exact Integrable.fintype_prod (fun i => fourierIntegrand_integrable ψ μ (g j i) (y i))
  have hs := integrable_finsetSum Finset.univ
    (fun j _ => (ht j).const_mul (c j))
  convert hs using 1
  funext x
  rw [hf x, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

private theorem rowFourierIntegral_sum
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) [SigmaFinite μ.measure] {d N : ℕ}
    (hdecomp : ∀ f : SchwartzBruhat (Fin d → F),
      ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Fin d → SchwartzBruhat F),
        ∀ x, f x = ∑ j, c j * ∏ i, g j i (x i))
    (c : Fin N → ℂ)
    (g : Fin N → SchwartzBruhat (Fin d → F)) (y : Fin d → F) :
    rowFourierIntegral ψ μ d (∑ j, c j • g j : SchwartzBruhat (Fin d → F)) y =
      ∑ j, c j * rowFourierIntegral ψ μ d (g j) y := by
  classical
  unfold rowFourierIntegral
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  simp_rw [mul_left_comm (ψ.complex _) (c _)]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => integral_const_mul (c j) _
  · intro j _
    exact (rowFourierIntegrand_integrable_of_decomposition ψ μ hdecomp (g j) y).const_mul (c j)

private theorem rowFourierCompatibility_of_scalar
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    [LocallyCompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    [SigmaFinite μ.measure]
    (hclosed : ∀ f : SchwartzBruhat F, ∃ g : SchwartzBruhat F,
      ∀ y, g y = fourierIntegral ψ μ f y)
    (hdecomp : ∀ f : SchwartzBruhat (Fin d → F),
      ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Fin d → SchwartzBruhat F),
        ∀ x, f x = ∑ j, c j * ∏ i, g j i (x i))
    (hsd : IsSelfDual ψ μ) : RowFourierClosed ψ μ d ∧ IsRowSelfDual ψ μ d := by
  classical
  have hmain (f : SchwartzBruhat (Fin d → F)) :
      ∃ k : SchwartzBruhat (Fin d → F), IsRowFourierPair ψ μ f k ∧
        ∀ y, rowFourierIntegral ψ μ d k y = f (-y) := by
    obtain ⟨N, c, g, hf⟩ := hdecomp f
    choose ghat hghat using fun j i => hclosed (g j i)
    have hf' : f = ∑ j, c j • rowTensor (g j) := by
      apply Subtype.ext
      funext x
      simpa [rowTensor] using hf x
    let k : SchwartzBruhat (Fin d → F) := ∑ j, c j • rowTensor (ghat j)
    refine ⟨k, ?_, ?_⟩
    · intro y
      rw [hf', rowFourierIntegral_sum ψ μ hdecomp]
      change (∑ j, c j • rowTensor (ghat j) : SchwartzBruhat (Fin d → F)) y = _
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      change (∏ i, ghat j i (y i)) =
        rowFourierIntegral ψ μ d (fun x => ∏ i, g j i (x i)) y
      rw [rowFourierIntegral_tensor]
      exact Finset.prod_congr rfl fun i _ => hghat j i (y i)
    · intro y
      change rowFourierIntegral ψ μ d
        (∑ j, c j • rowTensor (ghat j) : SchwartzBruhat (Fin d → F)) y = _
      rw [rowFourierIntegral_sum ψ μ hdecomp, hf (-y)]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      change rowFourierIntegral ψ μ d (fun x => ∏ i, ghat j i (x i)) y = _
      rw [rowFourierIntegral_tensor]
      apply Finset.prod_congr rfl
      intro i _
      have hi : (ghat j i : F → ℂ) = fourierTransform ψ μ (g j i) :=
        funext (hghat j i)
      rw [hi]
      exact (hsd (g j i)).2 (y i)
  constructor
  · intro f
    obtain ⟨k, hk, _⟩ := hmain f
    exact ⟨k, hk⟩
  · intro f
    obtain ⟨k, hk, hinv⟩ := hmain f
    have heq : rowFourierIntegral ψ μ d f = (k : (Fin d → F) → ℂ) :=
      funext fun y => (hk y).symm
    constructor
    · intro y
      rw [heq]
      exact rowFourierIntegrand_integrable_of_decomposition ψ μ hdecomp k y
    · intro y
      rw [heq]
      exact hinv y

/-- Scalar self-duality gives row Fourier closure and inversion in every finite
dimension, with convergence of the second integral. -/
theorem rowFourierCompatibility
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
    [TotallyDisconnectedSpace F] (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (d : ℕ) :
    RowFourierCompatibilityStatement ψ μ d := by
  intro hself
  obtain ⟨hσ, hclosed⟩ := scalarFourierClosure F ψ μ hself
  let : SigmaFinite μ.measure := hσ
  exact rowFourierCompatibility_of_scalar ψ μ hclosed (rowTensorDecomposition F d) hself

end Langlands.HarmonicAnalysis
