import Langlands.Representation.Whittaker.GeneralizedCoefficientKernelStatement
import Langlands.Representation.Whittaker.GeneralizedCoefficientDescent
import Langlands.Representation.Hecke.AntiPullback

/-! # The generalized-coefficient kernel criterion -/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

section Symmetry

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ] [IsInvInvariant μ]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (τ : G ≃ₜ G) (hτmul : ∀ g h : G, τ (g * h) = τ h * τ g)
variable (hτμ : MeasurePreserving τ μ μ)

include hτmul hτμ

/-- Distribution invariance exchanges the two convolution factors after pullback. -/
theorem generalizedCoefficient_convolution_symmetry
    (ℓ : Module.Dual ℂ V) (η : Module.Dual ℂ (SmoothDual ρ))
    (hInvariant : Distribution.pushforward τ (generalizedCoefficient μ ρ hρ ℓ η) =
      generalizedCoefficient μ ρ hρ ℓ η)
    (f g : SchwartzBruhat G) :
    generalizedCoefficient μ ρ hρ ℓ η (Hecke.TestFunction.convolution μ f g) =
      generalizedCoefficient μ ρ hρ ℓ η
        (Hecke.TestFunction.convolution μ
          (Hecke.TestFunction.pullback τ g) (Hecke.TestFunction.pullback τ f)) := by
  have h := congrArg
    (fun D : Distribution G => D (Hecke.TestFunction.convolution μ f g)) hInvariant
  simpa only [Distribution.pushforward_apply,
    Hecke.TestFunction.pullback_convolution μ τ hτmul hτμ] using h.symm

/-- Invariance of the two generalized coefficients forces inclusion of their
smoothing kernels, provided the first algebraic functional is nonzero. -/
theorem smoothFunctional_ker_le_of_generalizedCoefficient_invariant
    (hAdm : IsAdmissible ρ) (hIrr : ρ.IsIrreducible)
    (ℓ₁ ℓ₂ : Module.Dual ℂ V) (η : Module.Dual ℂ (SmoothDual ρ))
    (hη : η ≠ 0) (hℓ₁ : ℓ₁ ≠ 0)
    (hInvariant₁ : Distribution.pushforward τ (generalizedCoefficient μ ρ hρ ℓ₁ η) =
      generalizedCoefficient μ ρ hρ ℓ₁ η)
    (hInvariant₂ : Distribution.pushforward τ (generalizedCoefficient μ ρ hρ ℓ₂ η) =
      generalizedCoefficient μ ρ hρ ℓ₂ η) :
    LinearMap.ker (smoothFunctional μ ρ hρ ℓ₁) ≤
      LinearMap.ker (smoothFunctional μ ρ hρ ℓ₂) := by
  by_cases hℓ₂ : ℓ₂ = 0
  · subst ℓ₂
    simp
  intro f hf
  change smoothFunctional μ ρ hρ ℓ₁ f = 0 at hf
  change smoothFunctional μ ρ hρ ℓ₂ f = 0
  have hleft₁ := (generalizedCoefficient_left_annihilator μ ρ hρ hAdm hIrr
    ℓ₁ η hη f).2 hf
  have hright₁ : ∀ q : SchwartzBruhat G,
      generalizedCoefficient μ ρ hρ ℓ₁ η
        (Hecke.TestFunction.convolution μ q (Hecke.TestFunction.pullback τ f)) = 0 := by
    intro q
    obtain ⟨g, rfl⟩ := (Hecke.TestFunction.pullback τ).surjective q
    rw [← generalizedCoefficient_convolution_symmetry μ ρ hρ τ hτmul hτμ
      ℓ₁ η hInvariant₁ f g]
    exact hleft₁ g
  have hηright := (generalizedCoefficient_right_annihilator μ ρ hρ hAdm hIrr
    ℓ₁ hℓ₁ η (Hecke.TestFunction.pullback τ f)).1 hright₁
  have hright₂ := (generalizedCoefficient_right_annihilator μ ρ hρ hAdm hIrr
    ℓ₂ hℓ₂ η (Hecke.TestFunction.pullback τ f)).2 hηright
  apply (generalizedCoefficient_left_annihilator μ ρ hρ hAdm hIrr ℓ₂ η hη f).1
  intro g
  rw [generalizedCoefficient_convolution_symmetry μ ρ hρ τ hτmul hτμ
    ℓ₂ η hInvariant₂ f g]
  exact hright₂ (Hecke.TestFunction.pullback τ g)

end Symmetry

/-- The complete generalized-coefficient criterion for unique scalar
proportionality in a submodule of the full algebraic dual. -/
theorem generalizedCoefficientKernel : GeneralizedCoefficientKernelStatement.{uG,uV} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ _ V _ _ ρ hAdm hIrr
    τ _hτinvol hτmul hτμ W η hη hInvariant ℓ₁ ℓ₂ hℓ₁
  have hker := smoothFunctional_ker_le_of_generalizedCoefficient_invariant
    μ ρ hAdm.1 τ hτmul hτμ hAdm hIrr ℓ₁.val ℓ₂.val η hη hℓ₁
    (hInvariant ℓ₁) (hInvariant ℓ₂)
  obtain ⟨c, hc, hUnique⟩ := existsUnique_smul_of_smoothFunctional_ker_le
    μ ρ hAdm.1 ℓ₁.val ℓ₂.val hker hAdm hIrr hℓ₁
  refine ⟨c, Subtype.ext hc, ?_⟩
  intro d hd
  apply hUnique d
  exact congrArg Subtype.val hd

end Langlands.Whittaker
