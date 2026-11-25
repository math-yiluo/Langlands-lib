/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.GenericFiniteness

/-!
# Locally quasi-finite morphisms do not raise dimension

For a locally quasi-finite morphism of schemes `f : V ⟶ X` (for instance an étale morphism) we
show `dim V ≤ dim X`: the fibres of `f` are discrete, so `f` maps a strict chain of
specializations to a strict chain of specializations.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- An étale morphism is locally quasi-finite. -/
instance (priority := 900) Etale.locallyQuasiFinite {V X : Scheme.{u}} (f : V ⟶ X) [Etale f] :
    LocallyQuasiFinite f := by
  constructor
  intro U hU W hW e
  let := (f.appLE U W e).hom.toAlgebra
  have : Algebra.FiniteType Γ(X, U) Γ(V, W) := f.finiteType_appLE hU hW e
  have : Algebra.FormallyUnramified Γ(X, U) Γ(V, W) := f.formallyUnramified_appLE hU hW e
  exact (inferInstance : Algebra.QuasiFinite Γ(X, U) Γ(V, W))

/-- **A locally quasi-finite morphism does not raise dimension**: `dim V ≤ dim X` for a locally
quasi-finite morphism `f : V ⟶ X`. -/
theorem topologicalKrullDim_le_of_locallyQuasiFinite {V X : Scheme.{u}} (f : V ⟶ X)
    [LocallyQuasiFinite f] : topologicalKrullDim V ≤ topologicalKrullDim X := by
  let g : TopologicalSpace.IrreducibleCloseds V → TopologicalSpace.IrreducibleCloseds X :=
    fun Z ↦ ⟨closure (f '' Z), (Z.isIrreducible.image f f.continuous.continuousOn).closure,
      isClosed_closure⟩
  refine Order.krullDim_le_of_strictMono g fun Z₁ Z₂ h ↦ ?_
  obtain ⟨z₁, hz₁⟩ := QuasiSober.sober Z₁.isIrreducible Z₁.isClosed
  obtain ⟨z₂, hz₂⟩ := QuasiSober.sober Z₂.isIrreducible Z₂.isClosed
  have hg (Z : TopologicalSpace.IrreducibleCloseds V) (z : V) (hz : IsGenericPoint z Z) :
      (g Z : Set X) = closure {f z} := by
    change closure (f '' Z) = _
    rw [← hz.def, closure_image_closure f.continuous, Set.image_singleton]
  have hle : (Z₁ : Set V) ⊆ Z₂ := h.le
  have hne : (Z₁ : Set V) ≠ Z₂ := fun e ↦ h.ne (SetLike.coe_injective e)
  refine lt_of_le_of_ne (fun x hx ↦ closure_mono (Set.image_mono hle) hx) fun e ↦ hne ?_
  have e' : closure {f z₁} = closure {f z₂} := by
    rw [← hg Z₁ z₁ hz₁, ← hg Z₂ z₂ hz₂, e]
  have hfz : f z₁ = f z₂ := (inseparable_iff_closure_eq.2 e').eq
  have hsp : z₂ ⤳ z₁ := hz₂.specializes (hle hz₁.mem)
  rw [← hz₁.def, ← hz₂.def, f.eq_of_specializes_of_eq hsp hfz.symm]

end AlgebraicGeometry
