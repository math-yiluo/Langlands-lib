/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Exterior sheafification on a finite-free open

## References

* Stacks Project, Tag 0BRT
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Limits in
private noncomputable def freeModuleCofan (R : Type u) [Ring R] (I : Type u) :
    Cofan (fun (_ : I) ↦ ModuleCat.of R R) :=
  Cofan.mk (ModuleCat.of R (I →₀ R))
    (fun i ↦ ModuleCat.ofHom (Finsupp.lsingle i))

open CategoryTheory.Limits in
private noncomputable def freeModuleCofanColimit (R : Type u) [Ring R] (I : Type u) :
    IsColimit (freeModuleCofan R I) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun s ↦ ModuleCat.freeDesc (↾fun i ↦ s.inj i 1)) ?_ ?_
  · intro s i
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change ModuleCat.freeDesc (↾fun i ↦ s.inj i 1) (ModuleCat.freeMk i) = _
    exact ModuleCat.freeDesc_apply _ i
  · intro s m hm
    apply ModuleCat.free_hom_ext
    intro i
    have h := CategoryTheory.congr_fun (hm i) (1 : R)
    rw [ModuleCat.freeDesc_apply]
    exact h

-- Finite free sheaves are evaluated as finite coproducts of the section ring.
open CategoryTheory.Limits in
private noncomputable def freeSectionsIso (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) [Finite I] (W : (Over U)ᵒᵖ) :
    (SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.obj W ≅
      ModuleCat.of ((X.ringCatSheaf.over U).obj.obj W)
        (I →₀ (X.ringCatSheaf.over U).obj.obj W) := by
  let E := SheafOfModules.evaluation.{u} (X.ringCatSheaf.over U) W
  have : E.Additive := by
    dsimp only [E, SheafOfModules.evaluation]
    infer_instance
  have : PreservesBiproductsOfShape I E :=
    preservesBiproductsOfShape_of_preservesProductsOfShape E
  have : PreservesColimitsOfShape (Discrete I) E :=
    preservesCoproductsOfShape_of_preservesBiproductsOfShape E
  exact (isColimitOfPreserves E (SheafOfModules.isColimitFreeCofan I)).coconePointUniqueUpToIso
    (freeModuleCofanColimit _ I)

open CategoryTheory.Limits in
private theorem freeSectionsIso_inv_single (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) [Finite I] (W : (Over U)ᵒᵖ) (i : I) :
    (freeSectionsIso X U I W).inv (Finsupp.single i 1) =
      (SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).val W := by
  let E := SheafOfModules.evaluation.{u} (X.ringCatSheaf.over U) W
  have : E.Additive := by
    dsimp only [E, SheafOfModules.evaluation]
    infer_instance
  have : PreservesBiproductsOfShape I E :=
    preservesBiproductsOfShape_of_preservesProductsOfShape E
  have : PreservesColimitsOfShape (Discrete I) E :=
    preservesCoproductsOfShape_of_preservesBiproductsOfShape E
  have h := IsColimit.comp_coconePointUniqueUpToIso_inv
    (isColimitOfPreserves (SheafOfModules.evaluation.{u} (X.ringCatSheaf.over U) W)
      (SheafOfModules.isColimitFreeCofan I))
    (freeModuleCofanColimit ((X.ringCatSheaf.over U).obj.obj W) I) (Discrete.mk i)
  exact CategoryTheory.congr_fun h (1 : X.presheaf.obj (op W.unop.left))

private noncomputable def freeSectionsBasis (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) [Finite I] (W : (Over U)ᵒᵖ) :
    Module.Basis I (X.presheaf.obj (op W.unop.left))
      ((SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.obj W) :=
  Finsupp.basisSingleOne.map (freeSectionsIso X U I W).symm.toLinearEquiv

private theorem freeSectionsBasis_apply (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) [Finite I] (W : (Over U)ᵒᵖ) (i : I) :
    freeSectionsBasis X U I W i =
      (SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).val W := by
  rw [freeSectionsBasis, Module.Basis.map_apply]
  change (freeSectionsIso X U I W).inv (Finsupp.single i 1) = _
  exact freeSectionsIso_inv_single X U I W i

private theorem freeSectionsBasis_natural (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) [Finite I] {W Z : (Over U)ᵒᵖ} (f : W ⟶ Z) (i : I) :
    (SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.map f
        (freeSectionsBasis X U I W i) = freeSectionsBasis X U I Z i := by
  rw [freeSectionsBasis_apply, freeSectionsBasis_apply]
  exact PresheafOfModules.sections_property _ f

private noncomputable def frameBasis (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r))) (W : (Over U)ᵒᵖ) :
    Module.Basis (Fin r) (X.presheaf.obj (op W.unop.left))
      (M.val.obj (op W.unop.left)) :=
  ((freeSectionsBasis X U (ULift.{u} (Fin r)) W).reindex Equiv.ulift).map
    ((SheafOfModules.evaluation _ W).mapIso e).symm.toLinearEquiv

private theorem frameBasis_natural (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    {W Z : (Over U)ᵒᵖ} (f : W ⟶ Z) (i : Fin r) :
    M.val.map ((Over.forget U).op.map f) (frameBasis X M U r e W i) =
      frameBasis X M U r e Z i := by
  simp only [frameBasis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    freeSectionsBasis_apply]
  change (M.over U).val.map f
      (e.inv.val.app W ((SheafOfModules.freeSection _).val W)) =
    e.inv.val.app Z ((SheafOfModules.freeSection _).val Z)
  rw [← PresheafOfModules.naturality_apply, PresheafOfModules.sections_property]

-- Elaborating pure wedges across the scheme and over-site module interfaces is expensive.
set_option backward.isDefEq.respectTransparency false in
private theorem frameExteriorBasis_natural (X : Scheme.{u}) (M : X.Modules)
    (n : ℕ) (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    {W Z : (Over U)ᵒᵖ} (f : W ⟶ Z) (s : Set.powersetCard (Fin r) n) :
    ((_root_.PresheafOfModules.exteriorPower (R := _) M.val n).map ((Over.forget U).op.map f))
        ((frameBasis X M U r e W).exteriorPower n s) =
      (frameBasis X M U r e Z).exteriorPower n s := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  refine ((_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _) M.val n
    ((Over.forget U).op.map f)) _).trans ?_
  apply congrArg (exteriorPower.ιMulti (X.presheaf.obj (op Z.unop.left)) n
    (M := M.val.obj (op Z.unop.left)))
  funext i
  exact frameBasis_natural X M U r e f _

-- The increasing wedge bases identify the restricted exterior presheaf with a free sheaf.
private theorem exteriorPresheaf_local_coordinates (X : Scheme.{u}) (M : X.Modules)
    (n : ℕ) (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    Nonempty
      (((PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj).obj
        (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)) ≅
        (SheafOfModules.free (R := X.ringCatSheaf.over U)
          (ULift.{u} (Set.powersetCard (Fin r) n))).val) := by
  classical
  refine ⟨PresheafOfModules.isoMk (fun W ↦
    (((frameBasis X M U r e W).exteriorPower n).equiv
      (freeSectionsBasis X U (ULift.{u} (Set.powersetCard (Fin r) n)) W)
      Equiv.ulift.symm).toModuleIso) ?_⟩
  intro W Z f
  apply ModuleCat.hom_ext
  apply ((frameBasis X M U r e W).exteriorPower n).ext
  intro s
  change
    ((frameBasis X M U r e Z).exteriorPower n).equiv
        (freeSectionsBasis X U (ULift.{u} (Set.powersetCard (Fin r) n)) Z)
        Equiv.ulift.symm
        (((_root_.PresheafOfModules.exteriorPower (R := _) M.val n).map ((Over.forget U).op.map f))
          ((frameBasis X M U r e W).exteriorPower n s)) =
      (SheafOfModules.free (R := X.ringCatSheaf.over U)
        (ULift.{u} (Set.powersetCard (Fin r) n))).val.map f
        (((frameBasis X M U r e W).exteriorPower n).equiv
          (freeSectionsBasis X U (ULift.{u} (Set.powersetCard (Fin r) n)) W)
          Equiv.ulift.symm ((frameBasis X M U r e W).exteriorPower n s))
  rw [frameExteriorBasis_natural, Module.Basis.equiv_apply, Module.Basis.equiv_apply]
  exact (freeSectionsBasis_natural X U _ f _).symm

-- A presheaf which is already a sheaf over U has an invertible restricted unit.
private theorem local_unit_isIso (X : Scheme.{u})
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) (U : X.Opens)
    (F : SheafOfModules.{u} (X.ringCatSheaf.over U))
    (e : ((PresheafOfModules.pushforward₀ (Over.forget U)
      X.ringCatSheaf.obj).obj P) ≅ F.val) :
    IsIso ((PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
  let T := PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  let S : SheafOfModules.{u} (X.ringCatSheaf.over U) :=
    ⟨T.obj P, (Presheaf.isSheaf_of_iso_iff
      ((PresheafOfModules.toPresheaf _).mapIso e)).mpr F.isSheaf⟩
  let q : S ⟶ ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).obj P).over U := ⟨T.map η⟩
  let J := Opens.grothendieckTopology X
  have hinj := Presheaf.isLocallyInjective_whisker
    (J.over U) J (Over.forget U) (CategoryTheory.toSheafify J P.presheaf)
  have hsurj := Presheaf.isLocallySurjective_whisker
    (J.over U) J (Over.forget U) (CategoryTheory.toSheafify J P.presheaf)
  have : IsIso ((SheafOfModules.toSheaf _).map q) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hinj, hsurj⟩
  have : IsIso q := isIso_of_reflects_iso q (SheafOfModules.toSheaf _)
  exact inferInstanceAs (IsIso ((SheafOfModules.forget _).map q))

-- Keep the original containment binder, which is not needed in the conclusion itself.
set_option linter.unusedVariables false in
/-- On a finite-free open, exterior sheafification preserves sectionwise exterior powers
and gives the free sheaf indexed by increasing subsets. -/
theorem exteriorSheaf_local_free_comparison (X : Scheme.{u}) (M : X.Modules)
    (n : ℕ) (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    Nonempty ((exteriorPower M n).over U ≅
      SheafOfModules.free (ULift.{u} (Set.powersetCard (Fin r) n))) ∧
    ∀ (V : X.Opens) (g : V ⟶ U),
      Function.Bijective
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).app (op V)) := by
  obtain ⟨c⟩ := exteriorPresheaf_local_coordinates X M n U r e
  let T := PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)
  have : IsIso (T.map η) := local_unit_isIso X _ U _ c
  constructor
  · exact ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso
      ((asIso (T.map η)).symm ≪≫ c)⟩
  · intro V g
    have : IsIso ((T.map η).app (op (Over.mk g))) :=
      inferInstanceAs (IsIso ((PresheafOfModules.evaluation _
        (op (Over.mk g))).map (T.map η)))
    exact (ConcreteCategory.isIso_iff_bijective ((T.map η).app (op (Over.mk g)))).mp this

end AlgebraicGeometry.Scheme.Modules
