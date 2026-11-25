/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # Flat-unit compatibility on raw section cohomology

Source: Stacks Project, Cohomology, Tags 02N7 and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option Elab.async true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
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

private theorem adjoint_homology_comparison_cycles
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) (U : D ⥤ C) [L.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [L.PreservesHomology] [PreservesFiniteLimits U] (adj : L ⊣ U)
    (S : ShortComplex D) :
    let P := S.map U
    let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel U)).inv
    P.homologyπ ≫ adj.homEquiv P.homology S.homology
        ((P.mapHomologyIso L).inv ≫ ShortComplex.homologyMap
          (S.mapNatTrans adj.counit)) = k ≫ U.map S.homologyπ := by
  dsimp only
  let P := S.map U
  let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel U)).inv
  have hk : k ≫ U.map S.iCycles = P.iCycles := by
    exact P.isoCyclesOfIsLimit_inv_ι _
  let φ : P.map L ⟶ S := S.mapNatTrans adj.counit
  have hc : (P.mapCyclesIso L).inv ≫ ShortComplex.cyclesMap φ =
      L.map k ≫ adj.counit.app S.cycles := by
    apply (cancel_mono S.iCycles).1
    rw [Category.assoc, ShortComplex.cyclesMap_i]
    change (P.mapCyclesIso L).inv ≫ (P.map L).iCycles ≫
      adj.counit.app S.X₂ = (L.map k ≫ adj.counit.app S.cycles) ≫ S.iCycles
    have hi : (P.mapCyclesIso L).inv ≫ (P.map L).iCycles = L.map P.iCycles := by
      rw [← ShortComplex.mapCyclesIso_hom_iCycles P L,
        Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hi]
    have hn := adj.counit.naturality S.iCycles
    change L.map (U.map S.iCycles) ≫ adj.counit.app S.X₂ =
      adj.counit.app S.cycles ≫ S.iCycles at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← L.map_comp, hk]
  apply (adj.homEquiv _ _).symm.injective
  rw [← adj.homEquiv_naturality_left, Equiv.symm_apply_apply,
    adj.homEquiv_counit, L.map_comp, Category.assoc]
  change L.map P.homologyπ ≫ ((P.mapHomologyIso L).inv ≫
    ShortComplex.homologyMap φ) = L.map k ≫ L.map (U.map S.homologyπ) ≫
    adj.counit.app S.homology
  rw [← Category.assoc, mapHomologyIso_inv_homologyπ,
    Category.assoc, ShortComplex.homologyπ_naturality, ← Category.assoc, hc]
  have hn := adj.counit.naturality S.homologyπ
  change L.map (U.map S.homologyπ) ≫ adj.counit.app S.homology =
    adj.counit.app S.cycles ≫ S.homologyπ at hn
  simp only [hn, Category.assoc]

namespace AlgebraicGeometry.Scheme.Modules

private theorem section_comparison_cycles {Y : Scheme.{uBC}}
    (K : CochainComplex (SheafOfModules.{uBC} Y.ringCatSheaf) ℕ)
    (p : ℕ) (V : Y.Opens) :
    let E := PresheafOfModules.toPresheaf.{uBC} Y.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
    let P := (K.sc p).map (SheafOfModules.forget.{uBC} Y.ringCatSheaf)
    let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ (K.sc p).cyclesIsKernel
      (SheafOfModules.forget.{uBC} Y.ringCatSheaf))).inv
    (P.map E).homologyπ ≫ (P.mapHomologyIso E).hom ≫
        E.map (sectionCohomologyTheta K p) =
      (P.mapCyclesIso E).hom ≫ E.map k ≫ Hom.app (K.sc p).homologyπ V := by
  dsimp only
  rw [← Category.assoc, homologyπ_mapHomologyIso_hom, Category.assoc,
    ← Functor.map_comp]
  have h := adjoint_homology_comparison_cycles
    (PresheafOfModules.sheafification.{uBC} (𝟙 Y.ringCatSheaf.obj))
    (SheafOfModules.forget.{uBC} Y.ringCatSheaf)
    (PresheafOfModules.sheafificationAdjunction.{uBC} (𝟙 Y.ringCatSheaf.obj)) (K.sc p)
  change _ ≫ (PresheafOfModules.toPresheaf.{uBC} Y.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)).map
      (((K.sc p).map (SheafOfModules.forget.{uBC} Y.ringCatSheaf)).homologyπ ≫
        sectionCohomologyTheta K p) = _
  rw [show ((K.sc p).map (SheafOfModules.forget.{uBC} Y.ringCatSheaf)).homologyπ ≫
      sectionCohomologyTheta K p = _ from h, Functor.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward false in
-- Comparing sheaf, presheaf and section functor presentations needs extra elaboration.
/-- The cycle calculation only uses exactness and an adjunction to pushforward. -/
private theorem flat_unit_raw_sections_of_adjunction {S S' : Scheme.{uBC}}
    (g : S' ⟶ S) (F : S.Modules ⥤ S'.Modules) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ pushforward g)
    (K : CochainComplex S.Modules ℕ) (p : ℕ) (V : S.Opens) :
    let A := F.mapHomologicalComplex (ComplexShape.up ℕ)
    let U := SheafOfModules.forget S.ringCatSheaf
    let U' := SheafOfModules.forget S'.ringCatSheaf
    let E := PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
    let E' := PresheafOfModules.toPresheaf S'.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S'.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op (g ⁻¹ᵁ V))
    ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso E).hom ≫
        E.map (sectionCohomologyTheta K p) ≫
        Hom.app (adj.homEquiv _ _ ((K.sc p).mapHomologyIso F).inv) V =
      HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
          (ComplexShape.up ℕ)).map ((adj.mapHomologicalComplex
            (ComplexShape.up ℕ)).unit.app K)) p ≫
        ((((U'.mapHomologicalComplex (ComplexShape.up ℕ)).obj (A.obj K)).sc p)
          |>.mapHomologyIso E').hom ≫ E'.map (sectionCohomologyTheta (A.obj K) p) := by
  dsimp only
  let T := K.sc p
  let K' := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let T' := T.map F
  let U := SheafOfModules.forget S.ringCatSheaf
  let U' := SheafOfModules.forget S'.ringCatSheaf
  let E := PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
  let E' := PresheafOfModules.toPresheaf S'.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation S'.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op (g ⁻¹ᵁ V))
  have : U.PreservesZeroMorphisms := inferInstanceAs
    ((SheafOfModules.forget S.ringCatSheaf).PreservesZeroMorphisms)
  have : U'.PreservesZeroMorphisms := inferInstanceAs
    ((SheafOfModules.forget S'.ringCatSheaf).PreservesZeroMorphisms)
  have : PreservesFiniteLimits U := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.forget S.ringCatSheaf))
  have : PreservesFiniteLimits U' := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.forget S'.ringCatSheaf))
  have : E.PreservesHomology := inferInstanceAs
    ((PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)).PreservesHomology)
  have : E'.PreservesHomology := inferInstanceAs
    ((PresheafOfModules.toPresheaf S'.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S'.Opensᵒᵖ AddCommGrpCat.{uBC}).obj
        (op (g ⁻¹ᵁ V))).PreservesHomology)
  let P := T.map U
  let P' := T'.map U'
  let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ T.cyclesIsKernel U)).inv
  let k' := (P'.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ T'.cyclesIsKernel U')).inv
  let c := (P.mapCyclesIso E).hom ≫ E.map k
  let c' := (P'.mapCyclesIso E').hom ≫ E'.map k'
  let η := ((adj.mapHomologicalComplex (ComplexShape.up ℕ)).unit.app K)
  let φ : P.map E ⟶ P'.map E' :=
    (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
    (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
      (ComplexShape.up ℕ)).map η)
  change (P.mapHomologyIso E).hom ≫ E.map (sectionCohomologyTheta K p) ≫
    Hom.app (adj.homEquiv _ _ (T.mapHomologyIso F).inv) V =
    ShortComplex.homologyMap φ ≫ (P'.mapHomologyIso E').hom ≫
      E'.map (sectionCohomologyTheta K' p)
  have hs : (P.map E).homologyπ ≫ (P.mapHomologyIso E).hom ≫
      E.map (sectionCohomologyTheta K p) = c ≫ Hom.app T.homologyπ V :=
    section_comparison_cycles K p V
  have ht : (P'.map E').homologyπ ≫ (P'.mapHomologyIso E').hom ≫
      E'.map (sectionCohomologyTheta K' p) = c' ≫
        Hom.app T'.homologyπ (g ⁻¹ᵁ V) :=
    section_comparison_cycles K' p (g ⁻¹ᵁ V)
  apply (cancel_epi (P.map E).homologyπ).1
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc (P.map E).homologyπ (P.mapHomologyIso E).hom, hs]
  rw [← Category.assoc, ShortComplex.homologyπ_naturality]
  simp only [Category.assoc]
  rw [ht]
  change c ≫ Hom.app T.homologyπ V ≫
    Hom.app (adj.homEquiv _ _ (T.mapHomologyIso F).inv) V =
    ShortComplex.cyclesMap φ ≫ c' ≫ Hom.app T'.homologyπ (g ⁻¹ᵁ V)
  have hi : c ≫ Hom.app T.iCycles V = (P.map E).iCycles := by
    change ((P.mapCyclesIso E).hom ≫ E.map k) ≫ E.map (U.map T.iCycles) = _
    have hk : k ≫ U.map T.iCycles = P.iCycles := P.isoCyclesOfIsLimit_inv_ι _
    rw [Category.assoc, ← E.map_comp, hk]
    exact P.mapCyclesIso_hom_iCycles E
  have hi' : c' ≫ Hom.app T'.iCycles (g ⁻¹ᵁ V) = (P'.map E').iCycles := by
    change ((P'.mapCyclesIso E').hom ≫ E'.map k') ≫ E'.map (U'.map T'.iCycles) = _
    have hk' : k' ≫ U'.map T'.iCycles = P'.iCycles := P'.isoCyclesOfIsLimit_inv_ι _
    rw [Category.assoc, ← E'.map_comp, hk']
    exact P'.mapCyclesIso_hom_iCycles E'
  have ha : (T.mapCyclesIso F).inv ≫ T'.iCycles = F.map T.iCycles := by
    rw [← T.mapCyclesIso_hom_iCycles F, Iso.inv_hom_id_assoc]
  have : Mono (Hom.app T'.iCycles (g ⁻¹ᵁ V)) := by
    change Mono (E'.map (U'.map T'.iCycles))
    infer_instance
  have hc : ShortComplex.cyclesMap φ ≫ c' =
      c ≫ Hom.app (adj.unit.app T.cycles) V ≫
        Hom.app (T.mapCyclesIso F).inv (g ⁻¹ᵁ V) := by
    apply (cancel_mono (Hom.app T'.iCycles (g ⁻¹ᵁ V))).1
    rw [Category.assoc, hi', ShortComplex.cyclesMap_i]
    have hn := congrArg (fun f ↦ Hom.app f V) (adj.unit.naturality T.iCycles)
    change Hom.app T.iCycles V ≫ Hom.app (adj.unit.app T.X₂) V =
      Hom.app (adj.unit.app T.cycles) V ≫ Hom.app (F.map T.iCycles) (g ⁻¹ᵁ V) at hn
    have ha' := congrArg (fun f ↦ Hom.app f (g ⁻¹ᵁ V)) ha
    change Hom.app (T.mapCyclesIso F).inv (g ⁻¹ᵁ V) ≫
      Hom.app T'.iCycles (g ⁻¹ᵁ V) = Hom.app (F.map T.iCycles) (g ⁻¹ᵁ V) at ha'
    simp only [Category.assoc]
    rw [ha', ← hn, ← Category.assoc, hi]
    rfl
  have hh : T.homologyπ ≫ adj.homEquiv _ _ (T.mapHomologyIso F).inv =
      adj.unit.app T.cycles ≫ (pushforward g).map
        ((T.mapCyclesIso F).inv ≫ T'.homologyπ) := by
    rw [← adj.homEquiv_naturality_left, mapHomologyIso_inv_homologyπ,
      adj.homEquiv_unit]
  have hh' := congrArg (fun f ↦ Hom.app f V) hh
  change Hom.app T.homologyπ V ≫
    Hom.app (adj.homEquiv _ _ (T.mapHomologyIso F).inv) V =
    Hom.app (adj.unit.app T.cycles) V ≫
      Hom.app (T.mapCyclesIso F).inv (g ⁻¹ᵁ V) ≫
        Hom.app T'.homologyπ (g ⁻¹ᵁ V) at hh'
  rw [hh']
  simpa only [Category.assoc] using
    (congrArg (fun f ↦ f ≫ Hom.app T'.homologyπ (g ⁻¹ᵁ V)) hc).symm


/-- Flat pullback's unit carries raw section classes to the mate of the inverse homology
comparison. This is the unit case, before composition with a map into a target complex.
Source: Stacks Project, Cohomology, Tags 02N7 and 01E4.
(blueprint: lem-weil-pbc-flat-unit-raw-sections).

Proof: Represent a section-complex homology class on V by a cycle. Apply the degreewise
adjunction unit; naturality for the differential makes its image a cycle on g inverse V.
Naturality for the cycle inclusion identifies this with the unit on the cycle sheaf.
Flatness makes tensor pullback exact, so its cycle and homology comparison isomorphisms
identify the image cycle and quotient with those of the pulled-back complex. Naturality
of the unit for the homology quotient gives the inverse comparison's adjoint on the class.
The sheafification comparison theta sends a cycle to its class in the homology sheaf:
this follows from the sheafification counit and its exact homology comparison.
Apply exact evaluation to this cycle identity. The two composites agree after the
surjective cycle-to-homology map of the section complex, so they agree as morphisms.
The same argument applies in degree zero and on the empty open; no invertibility of theta
and no acyclicity of sections is used. -/
theorem flatUnit_raw_sections {S S' : Scheme.{uBC}} (g : S' ⟶ S) [Flat g]
    (K : CochainComplex S.Modules ℕ) (p : ℕ) (V : S.Opens) :
    let A := (tensorPullback g).mapHomologicalComplex (ComplexShape.up ℕ)
    let U := SheafOfModules.forget S.ringCatSheaf
    let U' := SheafOfModules.forget S'.ringCatSheaf
    let E := PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
    let E' := PresheafOfModules.toPresheaf S'.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S'.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op (g ⁻¹ᵁ V))
    let adj := Classical.choose (exists_tensorPullbackAdjunction g)
    ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso E).hom ≫
        E.map (sectionCohomologyTheta K p) ≫
        Hom.app (adj.homEquiv _ _ ((K.sc p).mapHomologyIso (tensorPullback g)).inv) V =
      HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
          (ComplexShape.up ℕ)).map ((adj.mapHomologicalComplex
            (ComplexShape.up ℕ)).unit.app K)) p ≫
        ((((U'.mapHomologicalComplex (ComplexShape.up ℕ)).obj (A.obj K)).sc p)
          |>.mapHomologyIso E').hom ≫ E'.map (sectionCohomologyTheta (A.obj K) p) := by
  exact flat_unit_raw_sections_of_adjunction g (tensorPullback g)
    (Classical.choose (exists_tensorPullbackAdjunction g)) K p V


end AlgebraicGeometry.Scheme.Modules
