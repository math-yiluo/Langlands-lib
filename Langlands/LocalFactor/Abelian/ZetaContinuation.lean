import Langlands.LocalFactor.Abelian.ZetaLaurentAlgebra

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

/-- A finite Euler--Laurent formula proves holomorphy of the convergent integral. -/
theorem zeta_differentiableOn_of_laurent_formula (π : F.Carrierˣ)
    (χ : Character) (a : ℕ) (μ : BorelMeasure T) (f : F.Carrier → ℂ)
    (A : ℤ →₀ ℂ)
    (hA : ∀ s, ConvergesAt T π χ s →
      zeta T μ f χ s = lFactorAt T π χ a s * laurentEvaluation T A s) :
    DifferentiableOn ℂ (zeta T μ f χ) {s | ConvergesAt T π χ s} := by
  have h : DifferentiableOn ℂ
      (fun s => lFactorAt T π χ a s * laurentEvaluation T A s)
      {s | ConvergesAt T π χ s} :=
    fun s hs => (analyticAt_lFactor_mul_laurent T π χ a A s
      (regularPoint_of_convergesAt T π χ a s hs)).differentiableAt.differentiableWithinAt
  exact h.congr hA

/-- A finite formula constructs the unique normal meromorphic continuation. -/
theorem existsUnique_extendsIntegral_of_laurent_formula (π : F.Carrierˣ)
    (χ : Character) (a : ℕ) (μ : BorelMeasure T) (f : F.Carrier → ℂ)
    (A : ℤ →₀ ℂ)
    (hA : ∀ s, ConvergesAt T π χ s →
      zeta T μ f χ s = lFactorAt T π χ a s * laurentEvaluation T A s) :
    ∃! Z : ℂ → ℂ, ExtendsIntegral T π μ f χ Z := by
  let Z := toMeromorphicNFOn
    (fun z => lFactorAt T π χ a z * laurentEvaluation T A z) Set.univ
  have hZ : ExtendsIntegral T π μ f χ Z := by
    refine ⟨meromorphicNFOn_toMeromorphicNFOn _ _, ?_⟩
    intro s hs
    exact (normalized_lFactor_mul_laurent_eq T π χ a A s
      (regularPoint_of_convergesAt T π χ a s hs)).trans (hA s hs).symm
  exact ⟨Z, hZ, fun Y hY => extendsIntegral_unique T π μ f χ hY hZ⟩

/-- The finite numerator gives both the punctured germs and regular values of any continuation. -/
theorem existsUnique_laurent_of_laurent_formula (π : F.Carrierˣ)
    (χ : Character) (a : ℕ) (μ : BorelMeasure T) (f : F.Carrier → ℂ)
    (A : ℤ →₀ ℂ)
    (hA : ∀ s, ConvergesAt T π χ s →
      zeta T μ f χ s = lFactorAt T π χ a s * laurentEvaluation T A s)
    (Z : ℂ → ℂ) (hZ : ExtendsIntegral T π μ f χ Z) :
    ∃! B : ℤ →₀ ℂ,
      (∀ s₀ : ℂ, Z =ᶠ[𝓝[≠] s₀]
        (fun s => lFactorAt T π χ a s * laurentEvaluation T B s)) ∧
      (∀ s, RegularPoint T π χ a s →
        Z s = lFactorAt T π χ a s * laurentEvaluation T B s) := by
  let Y := toMeromorphicNFOn
    (fun z => lFactorAt T π χ a z * laurentEvaluation T A z) Set.univ
  have hY : ExtendsIntegral T π μ f χ Y := by
    refine ⟨meromorphicNFOn_toMeromorphicNFOn _ _, ?_⟩
    intro s hs
    exact (normalized_lFactor_mul_laurent_eq T π χ a A s
      (regularPoint_of_convergesAt T π χ a s hs)).trans (hA s hs).symm
  have hZY : Z = Y := extendsIntegral_unique T π μ f χ hZ hY
  refine ⟨A, ⟨?_, ?_⟩, ?_⟩
  · intro s₀
    rw [hZY]
    exact (meromorphicOn_lFactor_mul_laurent T π χ a A).toMeromorphicNFOn_eq_self_on_nhdsNE
      (Set.mem_univ s₀)
  · intro s hs
    rw [hZY]
    exact normalized_lFactor_mul_laurent_eq T π χ a A s hs
  · intro B hB
    obtain ⟨s, hs⟩ := exists_convergesAt T π χ
    apply laurentEvaluation_eq_of_eventuallyEq T (s := s)
    filter_upwards [(isOpen_convergesAt T π χ).mem_nhds hs] with t ht
    have he := (hB.2 t (regularPoint_of_convergesAt T π χ a t ht)).symm.trans
      ((hZ.2 t ht).trans (hA t ht))
    exact mul_left_cancel₀
      (lFactorAt_ne_zero_of_regular T π χ a t
        (regularPoint_of_convergesAt T π χ a t ht)) he

end Langlands.LocalFactor.PadicAbelian
