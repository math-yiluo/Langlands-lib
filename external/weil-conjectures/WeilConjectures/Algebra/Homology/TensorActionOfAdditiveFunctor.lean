/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor coefficient actions from an additive functor

Source: Stacks Project, Tag 06Y6, functorial coefficient actions
(blueprint: lem-pc-tensor-action-additive-functor).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe uR uA uB v

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

private theorem action_of_endomorphisms
    (R : Type uR) (A : Type uA) (B : Type uB)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (M : ModuleCat.{v} B)
    (φ : A →+* Module.End B M)
    (hφ : ∀ r : R, φ (algebraMap R A r) =
      algebraMap B (Module.End B M) (algebraMap R B r)) :
    ∃ (T : ModuleCat.{v} (A ⊗[R] B))
      (e : (restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj T ≅ M),
      ∀ a : A,
        (restrictScalars (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
          ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 T) ≫ e.hom =
        e.hom ≫ ofHom (φ a) := by
  let : Algebra R (Module.End B M) :=
    Algebra.compHom (Module.End B M) (algebraMap R B)
  let : IsScalarTower R B (Module.End B M) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let f : A →ₐ[R] Module.End B M := { φ with commutes' := hφ }
  let g : B →ₐ[R] Module.End B M := IsScalarTower.toAlgHom R B (Module.End B M)
  have hfg : ∀ a b, Commute (f a) (g b) := by
    intro a b
    exact (Algebra.commutes b (f a)).symm
  let ρ := Algebra.TensorProduct.lift f g hfg
  let : Module (A ⊗[R] B) M := Module.compHom M ρ.toRingHom
  let T := ModuleCat.of (A ⊗[R] B) M
  let U := (restrictScalars (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj T
  have hright (b : B) (x : M) : (ρ (Algebra.TensorProduct.includeRight b)) x = b • x := by
    simp [ρ, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.lift_tmul, g]
  let e : U ≅ M :=
    { hom := ofHom (X := U) (Y := M)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun b x ↦ hright b x }
      inv := ofHom (X := M) (Y := U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun b x ↦ (hright b x).symm }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }
  refine ⟨T, e, ?_⟩
  intro a
  ext x
  change (ρ (Algebra.TensorProduct.includeLeft (S := R) a)) x = (φ a) x
  simp [ρ, Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.lift_tmul, f]

-- The coefficient actions use explicit module carriers.
/-- Source: Stacks Project, Tag 06Y6, functorial coefficient actions
(blueprint: lem-pc-tensor-action-additive-functor).

Proof: The additive functor induces a ring map on endomorphisms. Compose it with
scalar multiplication by A. Its restriction to R is scalar multiplication through B
by hR. B-linear endomorphisms commute with B-scalars. The algebra tensor universal
property therefore yields a ring map from A tensor B to B-linear endomorphisms.
Restrict the evaluation module along this ring map. The underlying B-module is the
original one because the restriction of the ring map to B is the scalar map.
The identity maps give the B-linear isomorphism, and the restriction to A gives
the required scalar equation. -/
theorem tensorAction_of_additiveFunctor
    (R : Type uR) (A : Type uA) (B : Type uB)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {C : Type*} [Category C] [Preadditive C] [CategoryTheory.Linear A C]
    (K : C ⥤ ModuleCat.{v} B) [K.Additive] (Q : C)
    (hR : ∀ r : R, K.map (algebraMap R A r • 𝟙 Q) =
      algebraMap R B r • 𝟙 (K.obj Q)) :
    ∃ (T : ModuleCat.{v} (A ⊗[R] B))
      (e : (restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj T ≅ K.obj Q),
      ∀ a : A,
        (restrictScalars (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
          ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 T) ≫ e.hom =
        e.hom ≫ K.map (a • 𝟙 Q) := by
  let M := K.obj Q
  let κ : End Q →+* End M :=
    { K.mapEnd Q with
      map_zero' := End.ext (K.map_zero Q Q)
      map_add' := fun _ _ ↦ End.ext K.map_add }
  let φ : A →+* Module.End B M :=
    (endRingEquiv M).toRingHom.comp (κ.comp (algebraMap A (End Q)))
  have hφ : ∀ r : R, φ (algebraMap R A r) =
      algebraMap B (Module.End B M) (algebraMap R B r) := by
    intro r
    change (K.map ((algebraMap A (End Q) (algebraMap R A r))).asHom).hom = _
    rw [Algebra.algebraMap_eq_smul_one]
    change (K.map (algebraMap R A r • 𝟙 Q)).hom = _
    rw [hR]
    rfl
  obtain ⟨T, e, he⟩ := action_of_endomorphisms R A B M φ hφ
  refine ⟨T, e, ?_⟩
  intro a
  convert he a using 1
  change e.hom ≫ K.map (a • 𝟙 Q) =
    e.hom ≫ K.map ((algebraMap A (End Q) a)).asHom
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

end ModuleCat
