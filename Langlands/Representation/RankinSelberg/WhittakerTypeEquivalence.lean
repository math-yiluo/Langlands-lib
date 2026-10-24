import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Whittaker.Transport

/-! Transport the full Whittaker-type predicate through actual representation equivalences. -/

namespace Langlands

universe uR uG uV uW uF

section Algebraic

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- An actual representation equivalence gives an equivalence over the group algebra. -/
def representationAsModuleEquiv (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[MonoidAlgebra R G] σ.asModule where
  __ := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  invFun := e.symm
  left_inv := e.toLinearEquiv.left_inv
  right_inv := e.toLinearEquiv.right_inv

@[simp]
theorem representationAsModuleEquiv_apply (e : ρ.Equiv σ) (v : ρ.asModule) :
    σ.asModuleEquiv (representationAsModuleEquiv e v) = e (ρ.asModuleEquiv v) := rfl

@[simp]
theorem representationAsModuleEquiv_symm_apply (e : ρ.Equiv σ) (w : σ.asModule) :
    ρ.asModuleEquiv ((representationAsModuleEquiv e).symm w) =
      e.symm (σ.asModuleEquiv w) := rfl

/-- Finite generation over the group algebra is invariant under representation equivalence. -/
theorem finite_asModule_iff_of_equiv (e : ρ.Equiv σ) :
    Module.Finite (MonoidAlgebra R G) ρ.asModule ↔
      Module.Finite (MonoidAlgebra R G) σ.asModule :=
  Module.Finite.equiv_iff (representationAsModuleEquiv e)

namespace Whittaker

variable {N : Subgroup G} {θ : N →* Rˣ}

/-- Transport the entire functional space by precomposition with the inverse equivalence. -/
def functionalsCongr (e : ρ.Equiv σ) :
    functionals N θ ρ ≃ₗ[R] functionals N θ σ where
  __ := functionalsComap e.symm.toIntertwiningMap
  invFun := functionalsComap e.toIntertwiningMap
  left_inv ℓ := by
    ext v
    change ℓ.val (e.symm (e v)) = ℓ.val v
    exact congrArg ℓ.val (e.toLinearEquiv.symm_apply_apply v)
  right_inv ℓ := by
    ext w
    change ℓ.val (e (e.symm w)) = ℓ.val w
    exact congrArg ℓ.val (e.toLinearEquiv.apply_symm_apply w)

@[simp]
theorem functionalsCongr_apply (e : ρ.Equiv σ) (ℓ : functionals N θ ρ) (w : W) :
    (functionalsCongr e ℓ).val w = ℓ.val (e.symm w) := rfl

@[simp]
theorem functionalsCongr_symm_apply (e : ρ.Equiv σ) (ℓ : functionals N θ σ) (v : V) :
    ((functionalsCongr e).symm ℓ).val v = ℓ.val (e v) := rfl

end Whittaker
end Algebraic

namespace RankinSelberg

open Whittaker GeneralLinear

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {θ : upperUnipotent (n + 1) F →* ℂˣ}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- All three clauses of Whittaker type transport through an actual equivalence. -/
theorem IsOfWhittakerType.of_equiv (hπ : IsOfWhittakerType n θ π) (e : π.Equiv σ) :
    IsOfWhittakerType n θ σ := by
  refine ⟨isAdmissible_of_equiv e hπ.1, (finite_asModule_iff_of_equiv e).mp hπ.2.1, ?_⟩
  obtain ⟨l⟩ := hπ.2.2
  exact ⟨(functionalsCongr e).symm.trans l⟩

/-- Whittaker type is invariant under equivalence, with independent carrier universes. -/
theorem isOfWhittakerType_iff_of_equiv (e : π.Equiv σ) :
    IsOfWhittakerType n θ π ↔ IsOfWhittakerType n θ σ :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

end RankinSelberg
end Langlands
