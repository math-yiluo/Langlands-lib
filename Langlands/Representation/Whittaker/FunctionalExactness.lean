import Langlands.Representation.Whittaker.LocalizationDual
import Langlands.Representation.Whittaker.Transport
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Pullback and exactness of actual character-equivariant functional spaces. -/

noncomputable section

namespace Langlands.Whittaker

universe uR uG uV uW uX

section Algebraic

variable {R : Type uR} [Field R] {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup X] [Module R X]
variable {ρ : Representation R G V} {σ : Representation R G W}
  {τ : Representation R G X}

/-- A surjective intertwiner gives injective pullback on equivariant functionals. -/
theorem functionalsComap_injective (U : Subgroup G) (θ : U →* Rˣ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    Function.Injective (functionalsComap (N := U) (θ := θ) f) := by
  intro ℓ m h
  apply Subtype.ext
  ext w
  obtain ⟨v, rfl⟩ := hf w
  exact congrArg (fun t : functionals U θ ρ => t.val v) h

/-- The published quotient-dual equivalence commutes with pullback. -/
theorem functionalsLocalizationDualEquiv_natural (U : Subgroup G) (θ : U →* Rˣ)
    (f : ρ.IntertwiningMap σ) (ℓ : functionals U θ σ) :
    functionalsLocalizationDualEquiv U θ ρ (functionalsComap (N := U) (θ := θ) f ℓ) =
      (functionalsLocalizationDualEquiv U θ σ ℓ).comp
        (Jacquet.Localization.mapLinear U θ f) := by
  apply Jacquet.Localization.hom_ext
  rfl

/-- The middle exactness of functional pullback is purely algebraic. -/
theorem functionalsComap_range_eq_ker (U : Subgroup G) (θ : U →* Rˣ)
    (i : ρ.IntertwiningMap σ) (p : σ.IntertwiningMap τ)
    (hp : Function.Surjective p)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    LinearMap.range (functionalsComap (N := U) (θ := θ) p) =
      LinearMap.ker (functionalsComap (N := U) (θ := θ) i) := by
  apply le_antisymm
  · rintro _ ⟨ℓ, rfl⟩
    apply Subtype.ext
    ext v
    have hpi : p (i v) = 0 := by
      change i v ∈ LinearMap.ker p.toLinearMap
      rw [← hex]
      exact ⟨v, rfl⟩
    change ℓ.val (p (i v)) = 0
    rw [hpi, map_zero]
  · intro ℓ hℓ
    have hℓi : functionalsComap (N := U) (θ := θ) i ℓ = 0 := hℓ
    have hk : ℓ.val ∈ (LinearMap.ker p.toLinearMap).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      rw [← hex] at hw
      obtain ⟨v, rfl⟩ := hw
      exact congrArg (fun t : functionals U θ ρ => t.val v) hℓi
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hk
    obtain ⟨L, hL⟩ := hk
    have hLp (w : W) : L (p w) = ℓ.val w := congrArg (fun t => t w) hL
    have hLθ : L ∈ functionals U θ τ := by
      intro u x
      obtain ⟨w, rfl⟩ := hp x
      rw [← p.isIntertwining, hLp, hLp]
      exact ℓ.property u w
    refine ⟨⟨L, hLθ⟩, ?_⟩
    apply Subtype.ext
    exact hL

end Algebraic

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- Character localization exactness gives extension of equivariant functionals
along every injective intertwiner into a smooth representation. -/
theorem functionalsComap_surjective_of_smooth
    (U : Subgroup G) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (θ : U →* ℂˣ) (hθloc : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i) (hσ : IsSmooth σ) :
    Function.Surjective (functionalsComap (N := U) (θ := θ) i) := by
  have hθinv : Jacquet.Localization.IsInvariant U ⊥ bot_le θ := by
    intro m u
    congr 1
    apply Subtype.ext
    have hm : (m : G) = 1 := m.property
    simp [Jacquet.Localization.conjugate, hm]
  let D := (Jacquet.Localization.map U θ ⊥ bot_le hθinv i).toLinearMap
  have hD : Function.Injective D :=
    Jacquet.Localization.map_injective_of_smooth U hU θ hθloc ⊥ bot_le hθinv i hi hσ
  intro ℓ
  obtain ⟨L, hL⟩ := LinearMap.dualMap_surjective_of_injective hD
    (functionalsLocalizationDualEquiv U θ ρ ℓ)
  refine ⟨(functionalsLocalizationDualEquiv U θ σ).symm L, ?_⟩
  apply Subtype.ext
  ext v
  exact congrArg (fun t => t (Jacquet.Localization.mk ρ U θ v)) hL

end Smooth

end Langlands.Whittaker
