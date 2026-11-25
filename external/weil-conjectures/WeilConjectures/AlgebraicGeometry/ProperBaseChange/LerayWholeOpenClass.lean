/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.Section.SectionCohomologyCycleFormula

/-! # The cocycle Leray edge on a restricted resolution

## References

* Stacks Project, Tags 01E4, 01F4 and 01FB
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
attribute [local irreducible] ShortComplex.mapHomologyIso ShortComplex.mapCyclesIso
  InjectiveResolution.isoRightDerivedObj
private theorem homologyπ_mapHomologyIso_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C) [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := ShortComplex.LeftHomologyData.canonical S
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% (h.map F).homologyπ_comp_homologyIso_hom]
  simp only [ShortComplex.LeftHomologyData.map_π]
  rw [← F.map_comp, h.π_comp_homologyIso_inv, F.map_comp]

private theorem mapHomologyIso_inv_homologyπ
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C) [F.PreservesLeftHomologyOf S] :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  rw [← cancel_epi (S.mapCyclesIso F).hom, ← reassoc_of% (homologyπ_mapHomologyIso_hom F S),
    Iso.hom_inv_id_assoc]
  simp

namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

attribute [local irreducible] moduleCohomologyFMap sectionCohomologyTheta
  resolutionSectionClass

set_option backward.defeqAttrib.useBackward false in
-- Compare the cycle kernels in the module, presheaf, and additive group categories.
private theorem sectionClass_top_cycle {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F) (n : ℕ)
    (s : (RingedSpace.globalSectionsComplex I).cycles n)
    (z : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj
      ((((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).cycles n))
    (hz : (I.cocomplex.X n).presheaf.map
        (eqToHom (congrArg op (Opens.map_top f.base).symm))
        ((RingedSpace.globalSectionsComplex I).iCycles n s) =
      (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
        ((((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles n) z) :
    let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
    let K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℕ :=
      ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    resolutionSectionClass I K ⊤ (Iso.refl _) n
        ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
          ((RingedSpace.globalSectionsComplex I).homologyπ n s)) =
      Hom.app (K.homologyπ n) ⊤ z := by
  dsimp only
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℕ :=
    ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let S := RingedSpace.globalSectionsComplex I
  let U := forget₂ (ModuleCat ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let P := (K.sc n).map (SheafOfModules.forget.{u} Y.ringCatSheaf)
  let k : P.cycles ⟶ (SheafOfModules.forget.{u} Y.ringCatSheaf).obj (K.cycles n) :=
    (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ (K.sc n).cyclesIsKernel
      (SheafOfModules.forget.{u} Y.ringCatSheaf))).inv
  let c : (P.map E).cycles ⟶
      E.obj ((SheafOfModules.forget.{u} Y.ringCatSheaf).obj (K.cycles n)) :=
    (P.mapCyclesIso E).hom ≫ E.map k
  let t : (P.map E).cycles := ((S.sc n).mapCyclesIso U).inv s
  have hi : c ≫ Hom.app (K.iCycles n) ⊤ = (P.map E).iCycles := by
    change ((P.mapCyclesIso E).hom ≫ E.map k) ≫
      E.map ((SheafOfModules.forget.{u} Y.ringCatSheaf).map (K.iCycles n)) = _
    have hk : k ≫ (SheafOfModules.forget.{u} Y.ringCatSheaf).map (K.iCycles n) =
        P.iCycles := P.isoCyclesOfIsLimit_inv_ι _
    rw [Category.assoc, ← E.map_comp, hk]
    exact P.mapCyclesIso_hom_iCycles E
  have ht : (P.map E).iCycles t = S.iCycles n s := by
    have h : ((S.sc n).mapCyclesIso U).inv ≫ ((S.sc n).map U).iCycles =
        U.map (S.iCycles n) := by
      rw [← (S.sc n).mapCyclesIso_hom_iCycles U, Iso.inv_hom_id_assoc]
      rfl
    exact ConcreteCategory.congr_hom h s
  have hm : Mono (Hom.app (K.iCycles n) ⊤) := by
    change Mono (((SheafOfModules.forget.{u} Y.ringCatSheaf) ⋙ E).map (K.iCycles n))
    infer_instance
  have hc : c t = z := by
    apply (AddCommGrpCat.mono_iff_injective (Hom.app (K.iCycles n) ⊤)).mp hm
    have hi' := ConcreteCategory.congr_hom hi t
    have hz' := hz
    simp only [eqToHom_refl] at hz'
    rw [(I.cocomplex.X n).presheaf.map_id] at hz'
    exact hi'.trans (ht.trans hz')
  have hp := ConcreteCategory.congr_hom (mapHomologyIso_inv_homologyπ U (S.sc n)) s
  have hclass := ConcreteCategory.congr_hom (section_comparison_cycles K n ⊤) t
  change (E.map (sectionCohomologyTheta K n))
      ((P.mapHomologyIso E).hom ((P.map E).homologyπ t)) =
    Hom.app (K.homologyπ n) ⊤ (c t) at hclass
  unfold resolutionSectionClass
  simp only [Iso.refl_hom]
  erw [CategoryTheory.Functor.map_id]
  change (E.map (sectionCohomologyTheta K n))
      ((P.mapHomologyIso E).hom (((S.sc n).mapHomologyIso U).inv
        ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).hom
          ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
            (S.homologyπ n s))))) = _
  rw [Iso.inv_hom_id_apply]
  change ((S.sc n).mapHomologyIso U).inv (S.homologyπ n s) =
    (P.map E).homologyπ t at hp
  exact (congrArg (fun x ↦ (E.map (sectionCohomologyTheta K n))
    ((P.mapHomologyIso E).hom x)) hp).trans
      (hclass.trans (congrArg (Hom.app (K.homologyπ n) ⊤) hc))

-- The edge formula and the resolution comparison use definitionally equal section functors.
/-- The whole-open resolution section class is the cocycle-defined Leray edge. -/
theorem whole_open_leray_edge {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (I : InjectiveResolution F) (n : ℕ) :
    let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
    let K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℕ :=
      ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    resolutionSectionClass I K ⊤ (Iso.refl _) n ≫
      Hom.app (I.isoRightDerivedObj (pushforward f) n).inv ⊤ =
    ((Classical.choose (exists_lerayEdge_isIso_of_vanishing f)) n).app F := by
  dsimp only
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℕ :=
    ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let S := RingedSpace.globalSectionsComplex I
  let U := forget₂ (ModuleCat ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}
  -- Compare after the epimorphisms from cycles to cohomology.
  apply (cancel_epi (U.map
    (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv)).1
  apply (cancel_epi (U.map (S.homologyπ n))).1
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨z, hz, he⟩ :=
    (Classical.choose_spec (exists_lerayEdge_isIso_of_vanishing f)).1 n F I K rfl s
  have hc := sectionClass_top_cycle f I n s z hz
  change Hom.app (I.isoRightDerivedObj (pushforward f) n).inv ⊤
    (resolutionSectionClass I K ⊤ (Iso.refl _) n
      ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
        (S.homologyπ n s))) = _
  have he' := he.symm
  simp only [eqToHom_refl, HomologicalComplex.homologyMap_id,
    Category.id_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply] at he'
  exact (congrArg (Hom.app (I.isoRightDerivedObj (pushforward f) n).inv ⊤) hc).trans he'

end AlgebraicGeometry.Scheme.Modules
