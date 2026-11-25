/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact

/-! # Construction of the symmetric algebra sheaf

Source: Stacks Project, Modules, Lemma 01CG (lemma-local-tensor-algebra).
(blueprint: lem-weil-pbc-symmetric-algebra-sheaf-construction).
-/

@[expose] public section


set_option autoImplicit false

universe u
open CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.SymmetricAlgebraSheaf
variable {X : Scheme.{u}} (F : X.Modules)

/-- Sectionwise symmetric algebra. -/
abbrev sections (U : X.Opensᵒᵖ) :=
  SymmetricAlgebra (X.presheaf.obj U) (F.val.obj U)

/-- Restriction extending module restriction by the symmetric algebra universal property. -/
noncomputable def restriction {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    sections F U →+* sections F V := by
  let : Algebra (X.presheaf.obj U) (sections F V) :=
    ((algebraMap (X.presheaf.obj V) (sections F V)).comp (X.presheaf.map i).hom).toAlgebra
  let f : F.val.obj U →ₗ[X.presheaf.obj U] sections F V :=
    { toFun := fun x ↦ SymmetricAlgebra.ι (X.presheaf.obj V) (F.val.obj V) (F.val.map i x)
      map_add' := by intro x y; simp
      map_smul' := by
        intro r x
        rw [F.val.map_smul]
        exact (SymmetricAlgebra.ι (X.presheaf.obj V) (F.val.obj V)).map_smul
          ((X.presheaf.map i) r) (F.val.map i x) }
  exact (SymmetricAlgebra.lift f).toRingHom

@[simp]
theorem restriction_ι {U V : X.Opensᵒᵖ} (i : U ⟶ V) (x : F.val.obj U) :
    restriction F i (SymmetricAlgebra.ι _ _ x) =
      SymmetricAlgebra.ι (X.presheaf.obj V) (F.val.obj V) (F.val.map i x) := by
  let : Algebra (X.presheaf.obj U) (sections F V) :=
    ((algebraMap (X.presheaf.obj V) (sections F V)).comp (X.presheaf.map i).hom).toAlgebra
  unfold restriction
  exact SymmetricAlgebra.lift_ι_apply _ x

@[simp]
theorem restriction_algebraMap {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (r : X.presheaf.obj U) :
    restriction F i (algebraMap (X.presheaf.obj U) (sections F U) r) =
      algebraMap (X.presheaf.obj V) (sections F V) (X.presheaf.map i r) := by
  let : Algebra (X.presheaf.obj U) (sections F V) :=
    ((algebraMap (X.presheaf.obj V) (sections F V)).comp (X.presheaf.map i).hom).toAlgebra
  unfold restriction
  exact AlgHom.commutes _ r

/-- The presheaf of sectionwise symmetric algebras. -/
noncomputable def presheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (sections F U)
  map i := CommRingCat.ofHom (restriction F i)
  map_id U := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    induction a using SymmetricAlgebra.induction with
    | algebraMap r => simp
    | ι x => simp
    | mul a b ha hb => simp_all
    | add a b ha hb => simp_all
  map_comp i k := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
        change restriction F (i ≫ k) (algebraMap _ _ r) =
          restriction F k (restriction F i (algebraMap _ _ r))
        rw [restriction_algebraMap, restriction_algebraMap, restriction_algebraMap]
        exact congrArg (algebraMap _ _) (CategoryTheory.congr_fun (X.presheaf.map_comp i k) r)
    | ι x =>
        change restriction F (i ≫ k) (SymmetricAlgebra.ι _ _ x) =
          restriction F k (restriction F i (SymmetricAlgebra.ι _ _ x))
        rw [restriction_ι, restriction_ι, restriction_ι]
        exact congrArg (SymmetricAlgebra.ι _ _) (F.val.map_comp_apply i k x)
    | mul a b ha hb => simp_all
    | add a b ha hb => simp_all

/-- The structure map into the sectionwise symmetric algebra presheaf. -/
noncomputable def structureMap : X.presheaf ⟶ presheaf F where
  app U := CommRingCat.ofHom (algebraMap _ _)
  naturality {U V} i := by
    apply CommRingCat.hom_ext
    ext r
    exact (restriction_algebraMap F i r).symm

/-- Ring sheafification of the sectionwise symmetric algebra, under the structure sheaf. -/
noncomputable def algebra : X.CommAlgebraSheaf :=
  Under.mk (show X.sheaf ⟶
    (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj (presheaf F) from
      ⟨structureMap F ≫ toSheafify (Opens.grothendieckTopology X) (presheaf F)⟩)

/-- Canonical section map into the symmetric algebra sheaf. -/
noncomputable def sectionMap (U : X.Opensᵒᵖ) :
    sections F U →+* (algebra F).right.obj.obj U :=
  ((toSheafify (Opens.grothendieckTopology X) (presheaf F)).app U).hom

/-- The degree-one map into the symmetric algebra sheaf. -/
noncomputable def inclusion : F ⟶ (algebra F).toModule where
  val :=
    { app U := ModuleCat.ofHom
        (Y := (algebra F).toModule.val.obj U)
        { toFun := fun x ↦ sectionMap F U (SymmetricAlgebra.ι _ _ x)
          map_add' := by intro x y; simp
          map_smul' := by
            intro r x
            change sectionMap F U (SymmetricAlgebra.ι _ _ (r • x)) =
              (algebra F).hom.hom.app U r * _
            change sectionMap F U (SymmetricAlgebra.ι _ _
              ((show X.presheaf.obj U from r) • x)) = _
            rw [map_smul, Algebra.smul_def]
            change sectionMap F U (algebraMap (X.presheaf.obj U) (sections F U) r * _) =
              (algebra F).hom.hom.app U r * _
            exact map_mul _ _ _ }
      naturality {U V} i := by
        ext x
        have h := (toSheafify (Opens.grothendieckTopology X) (presheaf F)).naturality i
        have hx := congrArg (fun t ↦ t (SymmetricAlgebra.ι _ _ x)) h
        change sectionMap F V (SymmetricAlgebra.ι _ _ (F.val.map i x)) =
          (algebra F).right.obj.map i (sectionMap F U (SymmetricAlgebra.ι _ _ x))
        change sectionMap F V (restriction F i (SymmetricAlgebra.ι _ _ x)) = _ at hx
        rw [restriction_ι] at hx
        exact hx }

end AlgebraicGeometry.SymmetricAlgebraSheaf
