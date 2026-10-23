import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-!
# Pullback of Whittaker functionals

Precomposition with an actual intertwiner preserves character equivariance.
Surjectivity preserves nonzeroness, and equivalences preserve genericity.
-/

namespace Langlands.Whittaker

universe uR uG uV uW uF

section Algebraic

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {N : Subgroup G} {θ : N →* Rˣ}
  {ρ : Representation R G V} {σ : Representation R G W}

/-- Pull back a character-equivariant functional by precomposition. -/
def functionalsComap (f : ρ.IntertwiningMap σ) :
    functionals N θ σ →ₗ[R] functionals N θ ρ where
  toFun ℓ := ⟨ℓ.val.comp f.toLinearMap, by
    intro n v
    change ℓ.val (f (ρ (n : G) v)) = (θ n : R) * ℓ.val (f v)
    rw [f.isIntertwining]
    exact ℓ.property n (f v)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem functionalsComap_apply (f : ρ.IntertwiningMap σ)
    (ℓ : functionals N θ σ) (v : V) :
    (functionalsComap f ℓ).val v = ℓ.val (f v) := rfl

/-- A nonzero functional stays nonzero after a surjective pullback. -/
theorem HasFunctional.of_surjective (hσ : HasFunctional (N := N) (θ := θ) σ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    HasFunctional (N := N) (θ := θ) ρ := by
  obtain ⟨ℓ, hℓ⟩ := hσ
  refine ⟨functionalsComap f ℓ, ?_⟩
  intro hzero
  apply hℓ
  ext w
  obtain ⟨v, rfl⟩ := hf w
  exact LinearMap.congr_fun hzero v

/-- Existence of a nonzero functional is invariant under representation equivalence. -/
theorem hasFunctional_iff_of_equiv (e : ρ.Equiv σ) :
    HasFunctional (N := N) (θ := θ) ρ ↔ HasFunctional (N := N) (θ := θ) σ :=
  ⟨fun h => h.of_surjective e.symm.toIntertwiningMap e.symm.toLinearEquiv.surjective,
    fun h => h.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective⟩

end Algebraic

section GeneralLinear

variable {F : Type uF} [CommRing F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F) (n : ℕ)
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- All three clauses of standard genericity transport through an actual equivalence. -/
theorem isGeneric_iff_of_equiv (e : π.Equiv τ) :
    IsGeneric ψ n π ↔ IsGeneric ψ n τ :=
  and_congr (Weil.IsomorphismInvariance.irreducible_iff e)
    (and_congr (isAdmissible_iff_of_equiv e) (hasFunctional_iff_of_equiv e))

end GeneralLinear

end Langlands.Whittaker
