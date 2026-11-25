/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.AlgebraicGeometry.DQCoheratorAdjunction
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Coherator detection for morphisms in the derived category

Source: Stacks Project, duality.tex, Tag 0B6I, final proof paragraph.
(blueprint: lem-pc-dq-coherator-derived-global-sections).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry

/-- An isomorphism after the coherator induces an isomorphism on derived global sections.
Source: Stacks Project, duality.tex, Tag 0B6I, final proof paragraph.
(blueprint: lem-pc-dq-coherator-derived-global-sections).

Proof: replace the source and target by K-injective complexes I and J. Full faithfulness
of the K-injective model represents the transported derived morphism by a chain map
s : I → J. Its image after the coherator is invertible, since the changes of
representatives are isomorphisms. Apply dqCoherator_detects_globalSections to s:
termwise global sections of s are a quasi-isomorphism. Localization therefore sends
this map to an isomorphism. The right-derived global-sections unit is invertible on
K-injectives and natural in s, identifying this localized map with derived global
sections of the original morphism. Transport back along the representative isomorphisms.
This works also for the zero morphism when its image under DQ is an isomorphism;
no quasi-coherence of the source or target is required. -/
theorem dqCoherator_isIso_derivedGlobalSections (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))]
    (DQ : schemeDerivedCategory Y ⥤ schemeDerivedQCohCategory Y)
    (adj : (schemeDerivedQCohProperty Y).ι ⊣ DQ)
    {E E' : schemeDerivedCategory Y} (s : E ⟶ E') [IsIso (DQ.map s)] :
    IsIso ((schemeDerivedGlobalSections Y).map s) := by
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let A := ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤))
  let F := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  obtain ⟨I, hI, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective E
  obtain ⟨J, hJ, ⟨j⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective E'
  let v := i.inv ≫ s ≫ j.hom
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj I) J).2
    (e.hom.app I ≫ v ≫ e.inv.app J)
  obtain ⟨r, rfl⟩ := q.map_surjective g
  have hr : DerivedCategory.Q.map r = v := by
    have hn := e.hom.naturality r
    dsimp only [Functor.comp_map] at hn
    rw [hg] at hn
    have hn' := congrArg (fun z ↦ e.inv.app I ≫ z) hn
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      Category.comp_id] using hn'.symm
  have : IsIso (DQ.map (DerivedCategory.Q.map r)) := by
    rw [hr]
    dsimp only [v]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    infer_instance
  have := dqCoherator_detects_globalSections Y DQ adj I J r
  have : IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map r)) :=
    inferInstance
  have hunit := F.rightDerivedFunctorUnit.naturality (q.map r)
  have hfac := (Functor.mapHomotopyCategoryFactors F (.up ℤ)).hom.naturality r
  dsimp only [Functor.comp_map] at hunit hfac
  have hmap : IsIso (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (q.map r))) := by
    have hn := (DerivedCategory.quotientCompQhIso A).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map r)
    dsimp only [Functor.comp_map] at hn
    have hfirst : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (.up ℤ)).map
          ((F.mapHomologicalComplex (.up ℤ)).map r))) := by
      apply (isIso_comp_right_iff _ ((DerivedCategory.quotientCompQhIso A).hom.app _)).mp
      rw [hn]
      infer_instance
    apply (isIso_comp_right_iff _
      (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryFactors F (.up ℤ)).hom.app J))).mp
    rw [← DerivedCategory.Qh.map_comp, hfac, DerivedCategory.Qh.map_comp]
    infer_instance
  have hder : IsIso (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (q.map r))) := by
    apply (isIso_comp_left_iff (F.rightDerivedFunctorUnit.app (q.obj I)) _).mp
    rw [← hunit]
    infer_instance
  have : IsIso ((schemeDerivedGlobalSections Y).map v) := by
    have hv : v = e.inv.app I ≫ DerivedCategory.Qh.map (q.map r) ≫ e.hom.app J := by
      rw [hg]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
        Category.comp_id]
    change IsIso (F.rightDerivedFunctor.map v)
    rw [hv, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    infer_instance
  have hs : s = i.hom ≫ v ≫ j.inv := by simp [v]
  rw [hs, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

end AlgebraicGeometry
