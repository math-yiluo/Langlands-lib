/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction

/-! # Core universal property for the symmetric algebra sheaf

## References

* Stacks Project, Modules, Lemmas 01CG and 01CL
* Stacks Project, Modules, Section 00DM
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

namespace SymmetricAlgebraSheaf

variable {X : Scheme.{u}} (F : X.Modules) (B : X.CommAlgebraSheaf)
  (f : F ⟶ B.toModule)

private noncomputable def sectionLift (U : X.Opensᵒᵖ) :
    sections F U →+* B.right.obj.obj U := by
  let : Algebra (X.presheaf.obj U) (B.right.obj.obj U) := (B.hom.hom.app U).hom.toAlgebra
  let l : F.val.obj U →ₗ[X.presheaf.obj U] B.right.obj.obj U :=
    { toFun := fun x ↦ f.val.app U x
      map_add' := map_add _
      map_smul' := by
        intro r x
        change (show B.right.obj.obj U from f.val.app U (r • x)) =
          B.hom.hom.app U r * (show B.right.obj.obj U from f.val.app U x)
        exact (f.val.app U).hom.map_smul r x }
  exact (SymmetricAlgebra.lift l).toRingHom

private theorem sectionLift_ι (U : X.Opensᵒᵖ) (x : F.val.obj U) :
    sectionLift F B f U (SymmetricAlgebra.ι _ _ x) = f.val.app U x := by
  let : Algebra (X.presheaf.obj U) (B.right.obj.obj U) := (B.hom.hom.app U).hom.toAlgebra
  unfold sectionLift
  exact SymmetricAlgebra.lift_ι_apply _ x

private theorem sectionLift_algebraMap (U : X.Opensᵒᵖ) (r : X.presheaf.obj U) :
    sectionLift F B f U (algebraMap _ _ r) = B.hom.hom.app U r := by
  let : Algebra (X.presheaf.obj U) (B.right.obj.obj U) := (B.hom.hom.app U).hom.toAlgebra
  unfold sectionLift
  exact AlgHom.commutes _ r

private noncomputable def liftPresheaf : presheaf F ⟶ B.right.obj where
  app U := CommRingCat.ofHom (sectionLift F B f U)
  naturality {U V} i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change sectionLift F B f V (restriction F i a) =
      B.right.obj.map i (sectionLift F B f U a)
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
        rw [restriction_algebraMap, sectionLift_algebraMap, sectionLift_algebraMap]
        exact CategoryTheory.congr_fun (B.hom.hom.naturality i) r
    | ι x =>
        rw [restriction_ι, sectionLift_ι, sectionLift_ι]
        exact PresheafOfModules.naturality_apply f.val i x
    | mul a b ha hb => simp only [map_mul, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]

private noncomputable def liftSheaf : (algebra F).right ⟶ B.right :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (liftPresheaf F B f) B.right.property⟩

private theorem liftSheaf_fac :
    toSheafify (Opens.grothendieckTopology X) (presheaf F) ≫
      (liftSheaf F B f).hom = liftPresheaf F B f :=
  toSheafify_sheafifyLift _ _ _

private noncomputable def liftAlgebra : algebra F ⟶ B :=
  Under.homMk (liftSheaf F B f) (by
    apply Sheaf.hom_ext
    change (structureMap F ≫ toSheafify _ (presheaf F)) ≫ (liftSheaf F B f).hom = _
    rw [Category.assoc, liftSheaf_fac]
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact sectionLift_algebraMap F B f U r)

end SymmetricAlgebraSheaf

/-- The sheafification has the symmetric-algebra universal property for its degree-one map. -/
theorem exists_quasiCoherentSymmetricAlgebra_core
    (X : Scheme.{u}) (F : X.Modules)
    (B : X.CommAlgebraSheaf) (f : F ⟶ B.toModule) :
    ∃! t : SymmetricAlgebraSheaf.algebra F ⟶ B,
      ∀ (U : X.Opens) (x : F.val.obj (op U)),
        (t.right.hom.app (op U)) ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x) =
          f.val.app (op U) x := by
  refine ⟨SymmetricAlgebraSheaf.liftAlgebra F B f, ?_, ?_⟩
  · intro U x
    have h := SymmetricAlgebraSheaf.liftSheaf_fac F B f
    have hx := congrArg
      (fun q ↦ q.app (op U) (SymmetricAlgebra.ι _ _ x)) h
    exact hx.trans (SymmetricAlgebraSheaf.sectionLift_ι F B f (op U) x)
  · intro t ht
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (Opens.grothendieckTopology X) _ _ B.right.property
    change toSheafify _ (SymmetricAlgebraSheaf.presheaf F) ≫ t.right.hom =
      toSheafify _ (SymmetricAlgebraSheaf.presheaf F) ≫
        (SymmetricAlgebraSheaf.liftSheaf F B f).hom
    rw [SymmetricAlgebraSheaf.liftSheaf_fac]
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change t.right.hom.app U (SymmetricAlgebraSheaf.sectionMap F U a) =
      SymmetricAlgebraSheaf.sectionLift F B f U a
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
        rw [SymmetricAlgebraSheaf.sectionLift_algebraMap]
        exact congrArg (fun q ↦ q.hom.app U r) (Under.w t)
    | ι x =>
        rw [SymmetricAlgebraSheaf.sectionLift_ι]
        exact ht U.unop x
    | mul a b ha hb => simp only [map_mul, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]

end AlgebraicGeometry
