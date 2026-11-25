/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Terminal sections as convolution global sections
Source: the constant-sheaf adjunction and tensor unit universal property.
(blueprint: lem-zl-section-ring-global-sections).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.MonObj
open scoped TensorProduct CategoryTheory.Obj
namespace CategoryTheory.InternalAbelianSheafModule

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [UnivLE.{max v w, u}]
  [HasSheafify J Ab.{u}] [(J.W (A := Ab.{u})).IsMonoidal]
  (R : Sheaf J Ab.{u}) [MonObj R] [IsCommMonObj R]

/-- Evaluation at the generator of the abelian tensor unit.
Source: free abelian group universal property and tensor multiplication
(blueprint: lem-zl-section-ring-global-sections). -/
def abelianGlobalEval (R : Ab.{u}) [MonObj R] :
    letI := ring R
    MonObj.Γ R →+* R := by
  letI := ring R
  refine { toFun := fun s ↦ s.hom.hom (ULift.up 1)
           map_one' := ?_
           map_mul' := ?_
           map_zero' := rfl
           map_add' := fun _ _ ↦ rfl }
  · change (η[R]).hom (ULift.up 1) = _
    rfl
  · intro f g
    change (μ[R]).hom
      (f.hom.hom (ULift.up 1) ⊗ₜ[ℤ] g.hom.hom (ULift.up 1)) = _
    rfl

/-- Evaluate a global tensor-unit section at the canonical integer section 1.
Source: tensor-unit universal property and the constant-sheaf adjunction
(blueprint: lem-zl-section-ring-global-sections). -/
def sectionGlobalEval (U : C) :
    MonObj.Γ R →+* (sectionRingSheaf J R).obj.obj (Opposite.op U) := by
  let F := sheafToPresheaf J Ab.{u}
  let E := (evaluation Cᵒᵖ Ab.{u}).obj (Opposite.op U)
  letI : E.Monoidal :=
    Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }
  letI : F.Additive := inferInstance
  letI : E.Additive := inferInstance
  letI := (F ⋙ E).monObjObj R
  exact (abelianGlobalEval ((F ⋙ E).obj R)).comp (MonObj.Γ.mapFunctor (F ⋙ E))

/-- Terminal evaluation is bijective on tensor-unit global sections.
Source: constant-sheaf adjunction and the free abelian group on one generator
(blueprint: lem-zl-section-ring-global-sections). -/
theorem sectionGlobalEval_bijective (U : C) (hU : IsTerminal U) :
    Function.Bijective (sectionGlobalEval J R U) := by
  let e := ((constantSheafAdj J Ab.{u} hU).homEquiv (𝟙_ Ab.{u}) R).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv (R.obj.obj (Opposite.op U))).toEquiv
  have h : (sectionGlobalEval J R U : MonObj.Γ R → _) = e := by
    funext s
    simp only [sectionGlobalEval, abelianGlobalEval]
    rfl
  rw [h]
  exact e.bijective

/-- The terminal section ring is the convolution ring of global sections.
Source: constant-sheaf adjunction and free abelian generator
(blueprint: lem-zl-section-ring-global-sections). -/
def sectionGlobalEquiv (U : C) (hU : IsTerminal U) :
    MonObj.Γ R ≃+* (sectionRingSheaf J R).obj.obj (Opposite.op U) :=
  RingEquiv.ofBijective (sectionGlobalEval J R U) (sectionGlobalEval_bijective J R U hU)

end CategoryTheory.InternalAbelianSheafModule
