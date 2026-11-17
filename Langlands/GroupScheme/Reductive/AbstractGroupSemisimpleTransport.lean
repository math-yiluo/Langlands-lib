import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Langlands.Representation.Tensor.Coordinates

/-! # Semisimplicity and finite coordinate transport -/

noncomputable section

universe u v w₁ w₂ w₃ w₄

open scoped MonoidAlgebra TensorProduct

namespace Langlands.RepresentationSemisimpleTransport

variable {k : Type u} [Field k] {G : Type v} [Monoid G]
  {V : Type w₁} [AddCommGroup V] [Module k V]
  {W : Type w₂} [AddCommGroup W] [Module k W]

/-- Invariance of a ground-field subspace under an abstract monoid representation. -/
def IsStable (ρ : Representation k G V) (U : Submodule k V) : Prop :=
  ∀ g v, v ∈ U → ρ g v ∈ U

/-- A nonzero invariant subspace with no smaller nonzero invariant subspace. -/
def IsSimple (ρ : Representation k G V) (U : Submodule k V) : Prop :=
  IsStable ρ U ∧ U ≠ ⊥ ∧
    ∀ U' : Submodule k V, IsStable ρ U' → U' ≤ U → U' = ⊥ ∨ U' = U

/-- Regard an invariant subspace as a Mathlib subrepresentation. -/
def subrepresentation (ρ : Representation k G V) (U : Submodule k V)
    (hU : IsStable ρ U) : Subrepresentation ρ :=
  ⟨U, fun g _ hv => hU g _ hv⟩

theorem isSimple_iff_isAtom (ρ : Representation k G V) (U : Subrepresentation ρ) :
    IsSimple ρ U.toSubmodule ↔ IsAtom U := by
  constructor
  · rintro ⟨_, hne, hmin⟩
    refine ⟨fun h => hne (congrArg Subrepresentation.toSubmodule h), ?_⟩
    intro U' hlt
    rcases hmin U'.toSubmodule
        (fun g _ hv => U'.apply_mem_toSubmodule g hv) hlt.le with h | h
    · exact Subrepresentation.toSubmodule_injective h
    · exact (hlt.ne (Subrepresentation.toSubmodule_injective h)).elim
  · intro h
    refine ⟨fun g _ hv => U.apply_mem_toSubmodule g hv, ?_, ?_⟩
    · intro he
      exact h.ne_bot (Subrepresentation.toSubmodule_injective he)
    · intro U' hU' hle
      rcases h.le_iff.mp (show subrepresentation ρ U' hU' ≤ U from hle) with h | h
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-- The complement and sum-of-simple-invariant-subspaces definitions agree. -/
theorem isSemisimple_iff_sSup_simples (ρ : Representation k G V) :
    ρ.IsSemisimpleRepresentation ↔
      sSup {U : Submodule k V | IsSimple ρ U} = ⊤ := by
  let e := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ))
  have hs (N : Submodule k[G] ρ.asModule) :
      IsSimple ρ (Subrepresentation.ofSubmodule' N).toSubmodule ↔
        IsSimpleModule k[G] N := by
    rw [isSimple_iff_isAtom, isSimpleModule_iff_isAtom]
    exact (e.symm.isAtom_iff N)
  have hset :
      Submodule.restrictScalars k '' {N : Submodule k[G] ρ.asModule |
        IsSimpleModule k[G] N} = {U : Submodule k V | IsSimple ρ U} := by
    ext U
    constructor
    · rintro ⟨N, hN, rfl⟩
      exact (hs N).mpr hN
    · intro hU
      let P := subrepresentation ρ U hU.1
      refine ⟨P.asSubmodule, ?_, rfl⟩
      exact (hs P.asSubmodule).mp hU
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    ← sSup_simples_eq_top_iff_isSemisimpleModule]
  rw [← hset]
  change sSup {N : Submodule k[G] ρ.asModule | IsSimpleModule k[G] N} = ⊤ ↔
    sSup (Submodule.restrictScalars k ''
      {N : Submodule k[G] ρ.asModule | IsSimpleModule k[G] N}) = ⊤
  rw [← Submodule.restrictScalars_sSup, Submodule.restrictScalars_eq_top_iff]

/-- Semisimplicity is invariant under an equivariant linear equivalence, with
independent universes for the two carriers. -/
theorem isSemisimple_iff_of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : ρ.IsSemisimpleRepresentation ↔ σ.IsSemisimpleRepresentation := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  exact LinearMap.isSemisimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap) e.bijective

/-- Conjugate a representation through an arbitrary linear coordinate equivalence. -/
def coordinates (ρ : Representation k G V) (e : V ≃ₗ[k] W) :
    Representation k G W :=
  e.conjRingEquiv.toMonoidHom.comp ρ

/-- Coordinate transport is an equivalence of representations. -/
def coordinatesEquiv (ρ : Representation k G V) (e : V ≃ₗ[k] W) :
    ρ.Equiv (coordinates ρ e) :=
  Representation.Equiv.mk e (by
    intro g
    ext x
    change e (ρ g x) = e (ρ g (e.symm (e x)))
    rw [e.symm_apply_apply])

theorem isSemisimple_coordinates_iff (ρ : Representation k G V) (e : V ≃ₗ[k] W) :
    (coordinates ρ e).IsSemisimpleRepresentation ↔ ρ.IsSemisimpleRepresentation :=
  (isSemisimple_iff_of_equiv (coordinatesEquiv ρ e)).symm

/-- Tensor two equivariant linear equivalences. -/
def tensorEquiv
    {V' : Type w₃} [AddCommGroup V'] [Module k V']
    {W' : Type w₄} [AddCommGroup W'] [Module k W']
    {ρ : Representation k G V} {ρ' : Representation k G V'}
    {σ : Representation k G W} {σ' : Representation k G W'}
    (e : ρ.Equiv ρ') (f : σ.Equiv σ') :
    (ρ.tprod σ).Equiv (ρ'.tprod σ') where
  toLinearEquiv := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  isIntertwining' g := (e.toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining' g

/-- A representation on an arbitrary finite-dimensional carrier has a finite
coordinate model in the coefficient-field universe. -/
def finiteCoordinates [FiniteDimensional k V] (ρ : Representation k G V) :
    Representation k G (Fin (Module.finrank k V) → k) :=
  coordinates ρ (Module.finBasis k V).equivFun

def finiteCoordinatesEquiv [FiniteDimensional k V] (ρ : Representation k G V) :
    ρ.Equiv (finiteCoordinates ρ) :=
  coordinatesEquiv ρ (Module.finBasis k V).equivFun

/-- Reducing the tensor-semisimplicity theorem to finite coordinate spaces
preserves all four independent universes. -/
theorem tensor_semisimple_of_coordinates
    (h : ∀ (n m : ℕ) (ρ : Representation k G (Fin n → k))
      (σ : Representation k G (Fin m → k)),
      ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation →
        (CoordinateTensor.representation ρ σ).IsSemisimpleRepresentation)
    [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    (hρ : ρ.IsSemisimpleRepresentation) (hσ : σ.IsSemisimpleRepresentation) :
    (ρ.tprod σ).IsSemisimpleRepresentation := by
  have hρ' := (isSemisimple_iff_of_equiv (finiteCoordinatesEquiv ρ)).mp hρ
  have hσ' := (isSemisimple_iff_of_equiv (finiteCoordinatesEquiv σ)).mp hσ
  have ht := h _ _ (finiteCoordinates ρ) (finiteCoordinates σ) hρ' hσ'
  exact (isSemisimple_iff_of_equiv
    ((tensorEquiv (finiteCoordinatesEquiv ρ) (finiteCoordinatesEquiv σ)).trans
      (CoordinateTensor.equiv _ _))).mpr ht

end Langlands.RepresentationSemisimpleTransport
