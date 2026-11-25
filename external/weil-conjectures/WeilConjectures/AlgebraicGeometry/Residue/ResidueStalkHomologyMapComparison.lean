/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ResidueField

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.LocalizedResidueHomologyRestriction
import WeilConjectures.AlgebraicGeometry.Localized.LocalizedStrictPerfectResidueHomology

/-! # Naturality of residue derived homology in a local perfect representative

## References

* Stacks Project, Tag 0E62, residue-field argument
* Tags 06YJ and 0D5S
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem strictlyPerfect_single_restricted_unit (S : Scheme.{u}) (U : S.Opens)
    (i : ℤ) :
    Scheme.IsStrictlyPerfect S U
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) i).obj
          ((SheafOfModules.overFunctor.{u}
            (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf))) := by
  classical
  let R := (moduleRings S.toRingedSpace).over U
  let M := (SheafOfModules.overFunctor.{u}
    (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf)
  let A := (CochainComplex.singleFunctor (SheafOfModules.{u} R) i).obj M
  refine ⟨⟨i, i, fun n hn ↦ ?_⟩, ?_⟩
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = i
    · subst n
      let e : A.X i ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin 1)) :=
        HomologicalComplex.singleObjXSelf (.up ℤ) i M ≪≫
          (coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit R)).symm
      exact ⟨1, e.hom, e.inv, e.hom_inv_id⟩
    · have hz : IsZero (A.X n) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      exact ⟨0, 0, 0, by simpa using (hz.eq_of_src (0 : A.X n ⟶ A.X n) (𝟙 _))⟩

/-- The representing chain arrow induces an isomorphism on residue stalk H⁰. -/
theorem isIso_residue_stalk_homologyMap (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ E) (s : S)
    (U : S.Opens) (hs : s ∈ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hP : Scheme.IsStrictlyPerfect S U P)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a)))
    (c : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit S.ringCatSheaf)) ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            ((SheafOfModules.overFunctor.{u}
              (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf))))
    (α : (CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
          ((SheafOfModules.overFunctor.{u}
            (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf)) ⟶ P)
    (hα : DerivedCategory.Q.map α = c.inv ≫
      (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory.map a ≫
        e.hom)
 :
    letI : (Scheme.Modules.overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    letI : (ModuleCat.extendScalars (IsLocalRing.residue
        (U.toScheme.presheaf.stalk ⟨s, hs⟩))).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (IsLocalRing.residue
        (U.toScheme.presheaf.stalk ⟨s, hs⟩))).left_adjoint_additive
    letI : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
        ⟨s, hs⟩).PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms U.toScheme.toRingedSpace ⟨s, hs⟩
    letI : ((Scheme.Modules.overEquiv U).functor ⋙
        RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩ ⋙
        ModuleCat.extendScalars (IsLocalRing.residue
          (U.toScheme.presheaf.stalk ⟨s, hs⟩))).PreservesZeroMorphisms :=
      { map_zero := by
          intro M N
          simp only [Functor.comp_map]
          rw [Functor.map_zero, Functor.map_zero, Functor.map_zero] }
    IsIso (HomologicalComplex.homologyMap
      ((((Scheme.Modules.overEquiv U).functor ⋙
        RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩ ⋙
        ModuleCat.extendScalars (IsLocalRing.residue
          (U.toScheme.presheaf.stalk ⟨s, hs⟩))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) 0) := by
  classical
  let : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (ModuleCat.extendScalars (IsLocalRing.residue
      (U.toScheme.presheaf.stalk ⟨s, hs⟩))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (IsLocalRing.residue
      (U.toScheme.presheaf.stalk ⟨s, hs⟩))).left_adjoint_additive
  let : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
      ⟨s, hs⟩).PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms U.toScheme.toRingedSpace ⟨s, hs⟩
  let : ((Scheme.Modules.overEquiv U).functor ⋙
      RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩ ⋙
      ModuleCat.extendScalars (IsLocalRing.residue
        (U.toScheme.presheaf.stalk ⟨s, hs⟩))).PreservesZeroMorphisms :=
    { map_zero := by
        intro M N
        simp only [Functor.comp_map]
        rw [Functor.map_zero, Functor.map_zero, Functor.map_zero] }
  let R := (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory
  let L := localizedResidueHomology S U ⟨s, hs⟩
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0
  let Γ := SheafOfModules.evaluation
      (moduleRings (Spec (S.residueField s)).toRingedSpace) (Opposite.op ⊤) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (S.residueField s)).inv.hom ⋙
    ModuleCat.extendScalars (U.ι.residueFieldMap ⟨s, hs⟩).hom
  obtain ⟨t⟩ := nonempty_localizedResidueHomology_restriction_iso S U ⟨s, hs⟩
  have hfac : L.map (R.map a) =
      (t.app _).hom ≫ Γ.map (H.map ((derivedPullback (S.fromSpecResidueField s)).map a)) ≫
        (t.app E).inv := by
    apply (cancel_mono (t.app E).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact t.hom.naturality a
  have hRa : IsIso (L.map (R.map a)) := by
    rw [hfac]
    infer_instance
  have hQα : IsIso (L.map (DerivedCategory.Q.map α)) := by
    rw [hα, L.map_comp, L.map_comp]
    infer_instance
  obtain ⟨b, hb⟩ := exists_localizedStrictPerfectResidueHomology_iso S U ⟨s, hs⟩
  have hA := strictlyPerfect_single_restricted_unit S U 0
  have hbα := hb _ P hA hP α
  have hcomp : IsIso (HomologicalComplex.homologyMap
      ((((Scheme.Modules.overEquiv U).functor ⋙
        RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩ ⋙
        ModuleCat.extendScalars (IsLocalRing.residue
          (U.toScheme.presheaf.stalk ⟨s, hs⟩))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) 0 ≫ (b P hP).hom) := by
    rw [hbα]
    exact inferInstance
  exact (isIso_comp_right_iff _ (b P hP).hom).mp hcomp

end AlgebraicGeometry
