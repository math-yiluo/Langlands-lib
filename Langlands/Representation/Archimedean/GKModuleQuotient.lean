import Langlands.Representation.KFiniteDual

/-! # Compact admissibility and `(𝔤, K)`-compatibility of quotients -/

noncomputable section

open scoped Matrix MonoidAlgebra TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

section Compact

variable {K V W : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ K V} {σ : Representation ℂ K W}

/-- A quotient of an admissible compact action with finite vectors and continuous coefficients
is admissible. -/
theorem IsAdmissibleGKModule.of_surjective (hρ : IsAdmissibleGKModule ρ)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (A : ρ.IntertwiningMap σ) (hA : Function.Surjective A) :
    IsAdmissibleGKModule σ := by
  have : IsSemisimpleModule ℂ[K] ρ.asModule := KFiniteDual.isSemisimpleModule hfin hcont
  intro d τ hτ
  have : Module.Finite ℂ (gkIntertwiners ρ d τ) := hρ d τ hτ
  let Φ : gkIntertwiners ρ d τ →ₗ[ℂ] gkIntertwiners σ d τ :=
    { toFun := fun T => ⟨A.toLinearMap ∘ₗ T.val, fun k x => by
        simp only [LinearMap.comp_apply, T.2 k x, Representation.IntertwiningMap.toLinearMap_apply,
          A.isIntertwining]⟩
      map_add' := fun S T => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c T => Subtype.ext (LinearMap.comp_smul _ _ _) }
  refine Module.Finite.of_surjective Φ fun T => ?_
  let τρ := KFiniteDual.matrixRep τ
  let t : τρ.IntertwiningMap σ := T.val.intertwiningMap_of_isIntertwiningMap τρ σ T.2
  let a := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ A
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property a hA
    (Representation.IntertwiningMap.equivLinearMapAsModule τρ σ t)
  let S := (Representation.IntertwiningMap.equivLinearMapAsModule τρ ρ).symm s
  refine ⟨⟨S.toLinearMap, S.isIntertwining⟩, Subtype.ext (LinearMap.ext fun x => ?_)⟩
  exact LinearMap.congr_fun hs x

end Compact

section Real

variable {n : ℕ} {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "L" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ

/-- The real `(𝔤, K)`-module axioms descend along a surjective intertwiner. -/
theorem IsRealGKModule.of_surjective
    {ρ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    {σ : Representation ℂ K W} {ψ : L →ₗ⁅ℂ⁆ Module.End ℂ W}
    (h : IsRealGKModule n ρ π) (A : ρ.IntertwiningMap σ) (hA : Function.Surjective A)
    (hL : ∀ X v, A (π X v) = ψ X (A v)) : IsRealGKModule n σ ψ := by
  refine ⟨fun y => ?_, fun y ℓ => ?_, fun γ X hγ hX y ℓ => ?_, fun k X y => ?_⟩
  · obtain ⟨x, rfl⟩ := hA y
    exact (h.1 x).map A
  · obtain ⟨x, rfl⟩ := hA y
    simpa only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
      A.isIntertwining] using h.2.1 x (ℓ ∘ₗ A.toLinearMap)
  · obtain ⟨x, rfl⟩ := hA y
    simpa only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
      A.isIntertwining, hL] using h.2.2.1 γ X hγ hX x (ℓ ∘ₗ A.toLinearMap)
  · obtain ⟨x, rfl⟩ := hA y
    simpa only [A.isIntertwining, hL] using congrArg A (h.2.2.2 k X x)

end Real

section Complex

variable {n : ℕ} {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

local notation "K" => Matrix.unitaryGroup (Fin n) ℂ
local notation "L" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ

/-- The complex `(𝔤, K)`-module axioms descend along a surjective intertwiner. -/
theorem IsComplexGKModule.of_surjective
    {ρ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    {σ : Representation ℂ K W} {ψ : L →ₗ⁅ℂ⁆ Module.End ℂ W}
    (h : IsComplexGKModule n ρ π) (A : ρ.IntertwiningMap σ) (hA : Function.Surjective A)
    (hL : ∀ X v, A (π X v) = ψ X (A v)) : IsComplexGKModule n σ ψ := by
  refine ⟨fun y => ?_, fun y ℓ => ?_, fun γ X hγ hX y ℓ => ?_, fun k X y => ?_⟩
  · obtain ⟨x, rfl⟩ := hA y
    exact (h.1 x).map A
  · obtain ⟨x, rfl⟩ := hA y
    simpa only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
      A.isIntertwining] using h.2.1 x (ℓ ∘ₗ A.toLinearMap)
  · obtain ⟨x, rfl⟩ := hA y
    simpa only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
      A.isIntertwining, hL] using h.2.2.1 γ X hγ hX x (ℓ ∘ₗ A.toLinearMap)
  · obtain ⟨x, rfl⟩ := hA y
    simpa only [A.isIntertwining, hL] using congrArg A (h.2.2.2 k X x)

end Complex

end Langlands.Archimedean
