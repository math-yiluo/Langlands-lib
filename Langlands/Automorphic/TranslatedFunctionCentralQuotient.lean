import Langlands.Automorphic.TranslatedBlockConstantTermOperators
import Langlands.Automorphic.FiniteCentralOrbit

/-! # Character selection on actual translated function spaces -/

noncomputable section

universe uA uR uV uW uX

set_option autoImplicit false

namespace Langlands.Automorphic

section CommutingActions

variable {R : Type uR} [Monoid R] {A : Type uA} [Monoid A]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ R V)
  (β : Representation ℂ A V) (h : ∀ a r, Commute (β a) (ρ r))

/-- A commuting action is linear over the monoid algebra of the original action. -/
def commutingRepresentationAsModule : A →* Module.End (MonoidAlgebra ℂ R) ρ.asModule where
  toFun a := Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ
    { toLinearMap := β a
      isIntertwining' r := (h a r).eq }
  map_one' := LinearMap.ext fun v => by
    change β 1 v = v
    rw [map_one]
    rfl
  map_mul' a b := LinearMap.ext fun v => by
    change β (a * b) v = β a (β b v)
    rw [map_mul]
    rfl

@[simp]
theorem commutingRepresentationAsModule_apply (a : A) (v : ρ.asModule) :
    commutingRepresentationAsModule ρ β h a v = β a v := rfl

end CommutingActions

section TranslatedQuotient

variable {R : Type uR} [Ring R] [Algebra ℂ R] {A : Type uA} [CommGroup A]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX}
  (β : Representation ℂ A (X → ℂ)) (φ : V →ₗ[ℂ] (X → ℂ))
  (ρ : R →ₐ[ℂ] Module.End ℂ V)
  (h : ∀ a v, v ∈ LinearMap.ker (translatedFunctionSum β φ) →
    finsuppCoefficientEnd A V (ρ a) v ∈ LinearMap.ker (translatedFunctionSum β φ))
  {W : Type uW} [AddCommGroup W] [Module (MonoidAlgebra ℂ R) W] [IsSimpleModule (MonoidAlgebra ℂ R) W]

local notation "𝓡" => MonoidAlgebra ℂ R
local notation "Γ" => AlgHom.toMonoidHom' (translatedFunctionOperatorAction β φ ρ h)
local notation "Γ₀" => AlgHom.toMonoidHom' ρ

/-- If the original coefficient quotient factors through evaluation, the same simple quotient
is retained by a cyclic subspace of the translated functions on which the centre acts by a character. -/
theorem exists_translatedFunction_centralCyclicQuotient
    (hfinite : ∀ v, FiniteVectors.IsFiniteVector β (φ v))
    (q : Representation.asModule Γ₀ →ₗ[𝓡] W) (hq : Function.Surjective q)
    (hker : ∀ v : Representation.asModule Γ₀, φ v = 0 → q v = 0) :
    ∃ (v : Representation.asModule Γ) (χ : A →* ℂˣ) (p : (𝓡 ∙ v) →ₗ[𝓡] W),
      Function.Surjective p ∧ ∀ a : A, translatedFunctionAction β φ a v = (χ a : ℂ) • v := by
  let σ := translatedFunctionAction β φ
  let z := commutingRepresentationAsModule Γ σ (translatedFunctionOperatorAction_commute β φ ρ h)
  let j := translatedFunctionOperatorMap β φ ρ h 1
  let f := Representation.IntertwiningMap.equivLinearMapAsModule Γ₀ Γ j
  have hf : LinearMap.ker f ≤ LinearMap.ker q := by
    intro v hv
    apply hker
    have hz : f v = 0 := hv
    have he : translatedFunctionEmbedding β φ (f v) = φ v := by
      let w : V := v
      change translatedFunctionSum β φ (Finsupp.single 1 w) = φ w
      rw [translatedFunctionSum_single, map_one, Module.End.one_apply]
    rw [← he, hz]
    exact (translatedFunctionEmbedding β φ).map_zero
  let p := (LinearMap.ker f).liftQ q hf ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  have hp : Function.Surjective p := by
    intro w
    obtain ⟨v, rfl⟩ := hq w
    refine ⟨⟨f v, LinearMap.mem_range_self f v⟩, ?_⟩
    change (LinearMap.ker f).liftQ q hf (f.quotKerEquivRange.symm ⟨f v, LinearMap.mem_range_self f v⟩) = q v
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hfin (v : Representation.asModule Γ) : Module.Finite ℂ (centralOrbitSpan z v) :=
    translatedFunctionAction_isFiniteVector β φ hfinite v
  exact exists_centralCharacter_cyclic_subquotient z hfin p hp

end TranslatedQuotient

end Langlands.Automorphic
