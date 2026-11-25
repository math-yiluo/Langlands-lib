/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Natural coefficient extension on complexes -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ModuleCat

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]

/-- Natural coefficient extension on complexes.
Source: Stacks Project, Tag 065Y, equation-comparison-map (Tag 065Z).
(blueprint: lem-pc-base-tensor-coefficient-natural-map).

Proof: the scalar-extension adjunction transposes the A-to-D unit, restricted
along R-to-A, to a B-linear map sending b tensor p to includeRight(b) tensor p.
The two R-actions coincide by the tensor-algebra balancing relation. This map
commutes with every A-linear map, by checking pure tensors and tensor induction.
Apply it degreewise: the same identity for the differential proves it is a chain
map, and the identity for a complex morphism proves naturality. This construction
also works for zero complexes and zero rings; no flatness is required. -/
theorem exists_baseTensorCoefficientNaturalMap :
    ∃ γ : (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
        (extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ) ⟶
      (extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ) ⋙
        (restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
          restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).mapHomologicalComplex
            (.up ℤ),
      ∀ (P : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ) (b : B) (p : P.X j),
        (γ.app P).f j (b ⊗ₜ[R, algebraMap R B] p) =
          (algebraMap (A ⊗[R] B) D (Algebra.TensorProduct.includeRight b) ⊗ₜ[A,
            (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))] p) := by
  let r := restrictScalars.{u} (algebraMap R A)
  let e := extendScalars.{u, u, u} (algebraMap R B)
  let l := extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
    (algebraMap A (A ⊗[R] B)))
  let s := restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
    restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom
  let adj := extendRestrictScalarsAdj.{u, u, u} (algebraMap R B)
  let adj' := extendRestrictScalarsAdj.{u, u, u}
    ((algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)))
  have heq : ((algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom).comp (algebraMap R B) =
      ((algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))).comp
        (algebraMap R A) := by
    ext x
    simp only [RingHom.comp_apply]
    congr 1
    exact (Algebra.TensorProduct.includeRight.commutes x).trans
      (Algebra.TensorProduct.includeLeft.commutes x).symm
  let c : restrictScalars.{u} ((algebraMap (A ⊗[R] B) D).comp
      (algebraMap A (A ⊗[R] B))) ⋙ r ⟶ s ⋙ restrictScalars.{u} (algebraMap R B) :=
    { app := fun M ↦ ofHom
        (X := ((restrictScalars.{u} ((algebraMap (A ⊗[R] B) D).comp
          (algebraMap A (A ⊗[R] B))) ⋙ r).obj M))
        (Y := (s ⋙ restrictScalars.{u} (algebraMap R B)).obj M)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro x m
            change (((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))).comp (algebraMap R A)) x • (show M from m) =
                (((algebraMap (A ⊗[R] B) D).comp
                  Algebra.TensorProduct.includeRight.toRingHom).comp (algebraMap R B)) x •
                    (show M from m)
            rw [heq] }
      naturality := by intros; ext x; rfl }
  let α : r ⟶ l ⋙ s ⋙ restrictScalars.{u} (algebraMap R B) :=
    Functor.whiskerRight adj'.unit r ≫ Functor.whiskerLeft l c
  let β : r ⋙ e ⟶ l ⋙ s :=
    { app := fun M ↦ (adj.homEquiv _ _).symm (α.app M)
      naturality := by
        intro M N a
        apply (adj.homEquiv _ _).injective
        dsimp only [Functor.comp_map]
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simpa only [Equiv.apply_symm_apply, Functor.comp_map] using α.naturality a }
  let γ : r.mapHomologicalComplex (.up ℤ) ⋙ e.mapHomologicalComplex (.up ℤ) ⟶
      l.mapHomologicalComplex (.up ℤ) ⋙ s.mapHomologicalComplex (.up ℤ) :=
    β.mapHomologicalComplex (.up ℤ)
  refine ⟨γ, ?_⟩
  intro P j b p
  let _ : Module R (s.obj (l.obj (P.X j))) := Module.compHom _ (algebraMap R B)
  change ((adj.homEquiv _ _).symm (α.app (P.X j))) (b ⊗ₜ[R, algebraMap R B] p) = _
  change (ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (algebraMap R B)
    (α.app (P.X j))) (b ⊗ₜ[R, algebraMap R B] p) = _
  erw [ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply, TensorProduct.lift.tmul]
  change (algebraMap (A ⊗[R] B) D (Algebra.TensorProduct.includeRight b)) •
    ((1 : D) ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
      (algebraMap A (A ⊗[R] B))] p) = _
  rw [ExtendScalars.smul_tmul, mul_one]

end ModuleCat
