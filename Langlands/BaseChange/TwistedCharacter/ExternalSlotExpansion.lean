import Langlands.BaseChange.ExternalTensorTwistedCharacter

/-! # Multilinear expansion of twisted characters of external tensor products -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

universe uI uG uV uW uS

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {H : ι → Type uG} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)]
  [∀ i, T2Space (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, TotallyDisconnectedSpace (H i)]
  [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
variable (μ : ∀ i, Measure (H i)) [∀ i, SigmaFinite (μ i)]
  [∀ i, IsFiniteMeasureOnCompacts (μ i)] [∀ i, (μ i).IsMulLeftInvariant]

omit [DecidableEq ι] [∀ i, Group (H i)] [∀ i, IsTopologicalGroup (H i)]
  [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)]
  [∀ i, TotallyDisconnectedSpace (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] in
/-- Two distributions on a finite product agree once they agree on pure tensors. -/
theorem distribution_ext_piTensor {D D' : Distribution (∀ i, H i)}
    (h : ∀ f : ∀ i, SchwartzBruhat (H i), D (SchwartzBruhat.piTensor f) =
      D' (SchwartzBruhat.piTensor f)) : D = D' := by
  apply LinearMap.ext
  intro f
  have hf : f ∈ Submodule.span ℂ (Set.range (SchwartzBruhat.piTensor (X := H))) := by
    rw [SchwartzBruhat.span_piTensor]
    exact Submodule.mem_top
  have hle : Submodule.span ℂ (Set.range (SchwartzBruhat.piTensor (X := H))) ≤
      LinearMap.ker (D - D') := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change D (SchwartzBruhat.piTensor g) - D' (SchwartzBruhat.piTensor g) = 0
    rw [h g, sub_self]
  have := hle hf
  change D f - D' f = 0 at this
  exact sub_eq_zero.mp this

variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- If each factor twisted distribution is a finite combination of other twisted
distributions, the twisted distribution of the external tensor product is the
corresponding multilinear combination. -/
theorem twistedDistribution_external_eq_sum
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (hρ : ∀ i, IsAdmissible (ρ i))
    (A : ∀ i, Module.End ℂ (V i))
    {S : ι → Type uS} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] (c : ∀ i, S i → ℂ)
    {W : ∀ i, S i → Type uW} [∀ i s, AddCommGroup (W i s)] [∀ i s, Module ℂ (W i s)]
    (σ : ∀ i s, Representation ℂ (H i) (W i s)) (hσ : ∀ i s, IsAdmissible (σ i s))
    (B : ∀ i s, Module.End ℂ (W i s))
    (h : ∀ i, twistedDistribution (μ i) (ρ i) (hρ i) (A i) =
      ∑ s, c i s • twistedDistribution (μ i) (σ i s) (hσ i s) (B i s)) :
    twistedDistribution (Measure.pi μ) (FiniteTensor.external ρ)
        (FiniteTensor.isAdmissible_external ρ hρ) (PiTensorProduct.map A) =
      ∑ t : (∀ i, S i), (∏ i, c i (t i)) •
        twistedDistribution (Measure.pi μ) (FiniteTensor.external (fun i => σ i (t i)))
          (FiniteTensor.isAdmissible_external _ (fun i => hσ i (t i)))
          (PiTensorProduct.map (fun i => B i (t i))) := by
  apply distribution_ext_piTensor
  intro f
  have hL : twistedDistribution (Measure.pi μ) (FiniteTensor.external ρ)
      (FiniteTensor.isAdmissible_external ρ hρ) (PiTensorProduct.map A)
        (SchwartzBruhat.piTensor f) =
      ∏ i, ∑ s, c i s * twistedDistribution (μ i) (σ i s) (hσ i s) (B i s) (f i) := by
    rw [twistedDistribution_external_piTensor μ ρ hρ A f]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [h i, LinearMap.sum_apply]
    rfl
  have hR (t : ∀ i, S i) : twistedDistribution (Measure.pi μ)
      (FiniteTensor.external (fun i => σ i (t i)))
      (FiniteTensor.isAdmissible_external _ (fun i => hσ i (t i)))
      (PiTensorProduct.map (fun i => B i (t i))) (SchwartzBruhat.piTensor f) =
      ∏ i, twistedDistribution (μ i) (σ i (t i)) (hσ i (t i)) (B i (t i)) (f i) :=
    twistedDistribution_external_piTensor μ _ _ _ f
  rw [hL, LinearMap.sum_apply, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [LinearMap.smul_apply, hR t, smul_eq_mul, ← Finset.prod_mul_distrib]

/-- The span form of `twistedDistribution_external_eq_sum`: if each factor twisted
distribution lies in the span of the twisted distributions of a class of admissible pairs,
the twisted distribution of the external tensor product lies in the span of the twisted
distributions of external tensor products of such pairs. -/
theorem twistedDistribution_external_mem_span
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (hρ : ∀ i, IsAdmissible (ρ i))
    (A : ∀ i, Module.End ℂ (V i))
    (Q : ∀ i, ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (H i) W),
      IsAdmissible σ → Module.End ℂ W → Prop)
    (h : ∀ i, twistedDistribution (μ i) (ρ i) (hρ i) (A i) ∈ Submodule.span ℂ
      {d | ∃ (W : Type uW) (iAdd : AddCommGroup W),
        letI := iAdd
        ∃ (iMod : Module ℂ W),
          letI := iMod
          ∃ (σ : Representation ℂ (H i) W) (hσ : IsAdmissible σ) (B : Module.End ℂ W),
            Q i W σ hσ B ∧ d = twistedDistribution (μ i) σ hσ B}) :
    twistedDistribution (Measure.pi μ) (FiniteTensor.external ρ)
        (FiniteTensor.isAdmissible_external ρ hρ) (PiTensorProduct.map A) ∈ Submodule.span ℂ
      {d | ∃ (W : ι → Type uW) (iAdd : ∀ i, AddCommGroup (W i)),
        letI := iAdd
        ∃ (iMod : ∀ i, Module ℂ (W i)),
          letI := iMod
          ∃ (σ : ∀ i, Representation ℂ (H i) (W i)) (hσ : ∀ i, IsAdmissible (σ i))
            (B : ∀ i, Module.End ℂ (W i)),
            (∀ i, Q i (W i) (σ i) (hσ i) (B i)) ∧
              d = twistedDistribution (Measure.pi μ) (FiniteTensor.external σ)
                (FiniteTensor.isAdmissible_external σ hσ) (PiTensorProduct.map B)} := by
  classical
  choose n c g hg using fun i => Submodule.mem_span_set'.mp (h i)
  choose W iAdd iMod σ hσ B hQ hd using fun i (k : Fin (n i)) => (g i k).property
  have hsum := twistedDistribution_external_eq_sum μ ρ hρ A c σ hσ B (fun i => by
    rw [← hg i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hd i k])
  rw [hsum]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨fun i => W i (t i), fun i => iAdd i (t i), fun i => iMod i (t i),
    fun i => σ i (t i), fun i => hσ i (t i), fun i => B i (t i), fun i => hQ i (t i), rfl⟩

end Langlands.BaseChange
