import Langlands.Global.Factors.HeckeDivisorEulerProduct
import Langlands.Global.Factors.HeckeConductorSupport

/-! # Actual finite Hecke Mellin series and their Fourier comparison -/

noncomputable section

universe u

namespace Langlands.Global.HeckeFunctionalEquation

open NumberField Langlands.HarmonicAnalysis
open Langlands.LocalFactor.PadicAbelian
open Langlands.Global.CompletionPadic
open HeckeDivisorEulerProduct

variable {K : Type u} [Field K] [NumberField K]

/-- The actual finite Euler-test Mellin divisor series. -/
def finiteMellin (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  ∑' d : FinitePlace K →₀ ℤ,
    DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d

/-- The actual Fourier Euler-test Mellin divisor series, retaining the zeroth
coefficients at every exceptional place. -/
def fourierFiniteMellin (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))
    (S : Finset (FinitePlace K)) (s : ℂ) : ℂ :=
  ∑' d : FinitePlace K →₀ ℤ,
    DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) d

/-- The finite Mellin series has the exact finite Euler product on a right half-plane. -/
theorem exists_finiteMellin_hasProd (χ : HeckeCharacter K) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Summable (fun d : FinitePlace K →₀ ℤ =>
        ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d‖) ∧
      HasProd (fun v => lFactor (topologicalData v) (χ.finiteComponent v) s)
        (finiteMellin χ s) :=
  exists_hasProd_shellWeight χ

/-- A common half-plane for both actual finite Euler-test series and the Fourier
series, with every supplied local component, scale and self-dual measure. -/
theorem exists_finiteMellin_common_halfPlane (χ : HeckeCharacter K)
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ x : K, ψ (diagonal K x) = 1)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (hf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))
    (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (hR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v))
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (hC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) :
    ∃ (σ : ℝ) (S : Finset (FinitePlace K)),
      (∀ v ∉ S, ∀ s : ℂ, fourierShellWeight χ ψf μ v s 0 = 1) ∧
      (∀ v ∉ S, ∀ s : ℂ, finiteEpsilon χ ψf μ v s = 1) ∧
      ∀ s : ℂ, σ < s.re →
        Summable (fun d : FinitePlace K →₀ ℤ =>
          ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d‖) ∧
        Summable (fun d : FinitePlace K →₀ ℤ =>
          ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ⁻¹ v s) d‖) ∧
        Summable (fun d : FinitePlace K →₀ ℤ =>
          ‖DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) d‖) ∧
        HasProd (fun v => lFactor (topologicalData v) (χ.finiteComponent v) s)
          (finiteMellin χ s) ∧
        HasProd (fun v => lFactor (topologicalData v) (χ⁻¹.finiteComponent v) s)
          (finiteMellin χ⁻¹ s) ∧
        HasProd (fun v => finiteEpsilon χ ψf μ v (1 - s) *
          lFactor (topologicalData v) (χ⁻¹.finiteComponent v) s)
          (fourierFiniteMellin χ ψf μ S s) ∧
        fourierFiniteMellin χ ψf μ S s =
          (∏ v ∈ S, finiteEpsilon χ ψf μ v (1 - s)) * finiteMellin χ⁻¹ s := by
  classical
  obtain ⟨Sψ, hSψ⟩ := exists_finset_additiveConductor_eq_zero ψ hdiag ψf hf aR hR aC hC
  obtain ⟨σf, S, hz, hε, hf⟩ := exists_hasProd_fourierShellWeight χ ψf μ Sψ hSψ
  obtain ⟨σχ, hχ⟩ := exists_hasProd_shellWeight χ
  obtain ⟨σd, hd⟩ := exists_hasProd_shellWeight χ⁻¹
  refine ⟨max σχ (max σd σf), S, hz, hε, fun s hs => ?_⟩
  have hrest : max σd σf < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  obtain ⟨hsc, hpc⟩ := hχ s (lt_of_le_of_lt (le_max_left _ _) hs)
  obtain ⟨hsd, hpd⟩ := hd s (lt_of_le_of_lt (le_max_left _ _) hrest)
  obtain ⟨hsf, hpf⟩ := hf s (lt_of_le_of_lt (le_max_right _ _) hrest)
  refine ⟨hsc, hsd, hsf, hpc, hpd, hpf, ?_⟩
  have hpε : HasProd (fun v => finiteEpsilon χ ψf μ v (1 - s))
      (∏ v ∈ S, finiteEpsilon χ ψf μ v (1 - s)) :=
    hasProd_prod_of_ne_finset_one (fun v hv => hε v hv (1 - s))
  exact hpf.unique (hpε.mul hpd)

end Langlands.Global.HeckeFunctionalEquation
