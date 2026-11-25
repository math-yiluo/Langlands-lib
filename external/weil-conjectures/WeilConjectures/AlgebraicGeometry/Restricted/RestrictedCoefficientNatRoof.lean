/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareLocalClassModels
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import all WeilConjectures.AlgebraicGeometry.Restricted.RestrictedRoofSectionModels
import all WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives

/-! # Natural indexed restricted coefficient roof

## References

* Stacks Project, Cohomology, Tags 01E4 and 01FB
-/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w vD uD vE uE vB uB
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

-- Expose only the category and complex wrappers used in instance matching.
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom
  HomologicalComplex.single
attribute [local irreducible] restrictionSectionsIso pushforwardRestrictIso
  restrictedDirectImageMap ModuleCohomologyFMapData.map moduleCohomologyFMap

private theorem roof_transport {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B : D} {I J K L M N : C}
    (m : A ⟶ B) (rI : A ⟶ H.obj I) (rJ : B ⟶ H.obj J)
    (mu : J ⟶ K) (b : I ⟶ K) (c : K ⟶ L)
    (sI : I ⟶ M) (sJ : J ⟶ N) (ell : N ⟶ L) (beta : M ⟶ L)
    (hd : m ≫ rJ ≫ H.map mu = rI ≫ H.map b)
    (hm : mu ≫ c = sJ ≫ ell) (hb : b ≫ c = sI ≫ beta) :
    m ≫ rJ ≫ H.map sJ ≫ H.map ell = rI ≫ H.map sI ≫ H.map beta := by
  have h := congrArg (fun z ↦ z ≫ H.map c) hd
  have hm' := congrArg H.map hm
  have hb' := congrArg H.map hb
  simp only [H.map_comp, Category.assoc] at hm' hb' h
  rw [hm', hb'] at h
  exact h

private theorem map_comp_post {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B E : C} {T : D} (f : A ⟶ B) (g : B ⟶ E)
    (c : H.obj E ⟶ T) :
    H.map (f ≫ g) ≫ c = H.map f ≫ (H.map g ≫ c) := by
  rw [H.map_comp, Category.assoc]

private theorem roof_denominator {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {K M L : C} {Q S T : D}
    (c : K ≅ M) (a : Q ≅ H.obj M) (rho : Q ⟶ S)
    (sK : H.obj K ⟶ S) (sL : H.obj L ⟶ T) (ell : K ⟶ L) (e : S ⟶ T)
    (hs : H.map c.hom ≫ a.inv ≫ rho = sK)
    (hn : H.map ell ≫ sL = sK ≫ e) :
    (a.hom ≫ H.map (c.inv ≫ ell)) ≫ sL = rho ≫ e := by
  rw [H.map_comp]
  simp only [Category.assoc]
  rw [hn, ← hs]
  simp only [Category.assoc, ← H.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_assoc]

private theorem regroup_six {C : Type*} [Category C] {A B D E F G K : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (e : F ⟶ G) (f : G ⟶ K) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = (a ≫ b) ≫ c ≫ d ≫ (e ≫ f) := by
  simp only [Category.assoc]

private theorem roof_formula_cancel {C : Type*} [Category C] {A B I J K : C}
    (rI : A ≅ I) (rJ : B ≅ J) (b : I ⟶ K) (mu : J ⟶ K) [hmu : IsIso mu] :
    (rI.hom ≫ b ≫ inv mu ≫ rJ.inv) ≫ rJ.hom ≫ mu = rI.hom ≫ b := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]

private def restrictedRoof_comparison {X Z : Scheme.{u}} (v : Z ⟶ X)
    {G : Z.Modules} (J : InjectiveResolution G) (U : X.Opens)
    (R' : RestrictedResolutionSections J (v ⁻¹ᵁ U)) :
    ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex) ≅
      ((pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj R'.resolution.cocomplex :=
  (NatIso.mapHomologicalComplex
    (pushforwardRestrictIso (coefficient_restriction_pullback v U))
    (ComplexShape.up ℕ)).app J.cocomplex ≪≫
      ((pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).mapHomologicalComplex
        (ComplexShape.up ℕ)).mapIso R'.comparison.symm

private theorem roof_denominator_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (r : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (s : r ⋙ G ≅ H)
    {K L : C} {M : D} {Q : E} (c : r.obj K ≅ M) (a : Q ≅ G.obj M)
    (rho : Q ⟶ H.obj K) (ell : K ⟶ L)
    (hs : G.map c.hom ≫ a.inv ≫ rho = s.hom.app K) :
    (a.hom ≫ G.map (c.inv ≫ r.map ell)) ≫ s.hom.app L = rho ≫ H.map ell :=
  roof_denominator G c a rho (s.hom.app K) (s.hom.app L)
    (r.map ell) (H.map ell) hs (s.hom.naturality ell)

private theorem coefficientData_roof_formula {X Y : Scheme.{u}} {v : X ⟶ Y}
    {F : SheafOfModules.{u} Y.ringCatSheaf} {G : SheafOfModules.{u} X.ringCatSheaf}
    {φ : F ⟶ (pushforward v).obj G} (D : ModuleCohomologyFMapData v F G φ) (q : ℕ) :
    let Γ := (RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) q
    let rI := (forget₂ _ AddCommGrpCat.{u}).mapIso
      (D.J.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Y.toRingedSpace) q) ≪≫
      (((RingedSpace.globalSectionsComplex D.J).sc q).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).symm
    let rJ := (forget₂ _ AddCommGrpCat.{u}).mapIso
      (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q) ≪≫
      (((RingedSpace.globalSectionsComplex D.I).sc q).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).symm
    D.map q ≫ rJ.hom ≫ H.map (D.a.hom ≫ Γ.map D.lambda) =
      rI.hom ≫ H.map (Γ.map D.β) := by
  intro Γ H rI rJ
  have : IsIso (H.map (D.a.hom ≫ Γ.map D.lambda)) := D.invertible q
  have he : D.map q = rI.hom ≫ H.map (Γ.map D.β) ≫
      inv (H.map (D.a.hom ≫ Γ.map D.lambda)) ≫ rJ.inv := by
    unfold ModuleCohomologyFMapData.map
    dsimp only [rI, rJ, Iso.trans, Iso.symm, Functor.mapIso]
    exact regroup_six _ _ _ _ _ _
  exact (congrArg (fun f ↦ f ≫ rJ.hom ≫ H.map (D.a.hom ≫ Γ.map D.lambda)) he).trans
    (roof_formula_cancel rI rJ (H.map (Γ.map D.β))
      (H.map (D.a.hom ≫ Γ.map D.lambda)) (hmu := D.invertible q))

-- Compare the explicit scheme-restriction and section-functor presentations.
/-- Restricting an augmented injective roof computes the classical coefficient map. -/
theorem restrictedCoefficient_natRoof {X Z : Scheme.{u}} (v : Z ⟶ X)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (pushforward v).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (L : CochainComplex X.Modules ℕ) (hL : ∀ n : ℕ, Injective (L.X n))
    (ell : ((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶ L)
    (hell : QuasiIso ell) (beta : I.cocomplex ⟶ L)
    (hbeta : I.ι.f 0 ≫ beta.f 0 = φ ≫ (pushforward v).map (J.ι.f 0) ≫ ell.f 0)
    (U : X.Opens) (R : RestrictedResolutionSections I U)
    (R' : RestrictedResolutionSections J (v ⁻¹ᵁ U)) (q : ℕ) :
    letI := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
    letI := RingedSpace.globalSectionsFunctor_additive (v ⁻¹ᵁ U).toScheme.toRingedSpace
    let Γ := (RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
      (ComplexShape.up ℕ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) q
    let rI := (forget₂ _ AddCommGrpCat.{u}).mapIso
      ((show InjectiveResolution (C := SheafOfModules.{u}
          (moduleRings U.toScheme.toRingedSpace)) ((restrictFunctor U.ι).obj F) from
          R.resolution).isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) q) ≪≫
      (((RingedSpace.globalSectionsComplex R.resolution).sc q).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).symm
    let rJ := (forget₂ _ AddCommGrpCat.{u}).mapIso
      ((show InjectiveResolution (C := SheafOfModules.{u}
          (moduleRings (v ⁻¹ᵁ U).toScheme.toRingedSpace))
            ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G) from R'.resolution).isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor (v ⁻¹ᵁ U).toScheme.toRingedSpace) q) ≪≫
      (((RingedSpace.globalSectionsComplex R'.resolution).sc q).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).symm
    moduleCohomologyFMap (v.resLE U (v ⁻¹ᵁ U) le_rfl)
      (restrictedDirectImageMap v φ U) q ≫ rJ.hom ≫ H.map R'.sections.hom ≫ H.map (Γ.map ell) =
      rI.hom ≫ H.map R.sections.hom ≫ H.map (Γ.map beta) := by
  intro Γ H rI rJ
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory,
    Scheme.Modules.instAbelian] at *
  let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive (v ⁻¹ᵁ U).toScheme.toRingedSpace
  let : (RingedSpace.openModuleSections X.toRingedSpace U).Additive :=
    RingedSpace.openModuleSections_additive X.toRingedSpace U
  let r := restrictFunctor U.ι
  let rC := r.mapHomologicalComplex (ComplexShape.up ℕ)
  let : PreservesFiniteLimits (SheafOfModules.overFunctor X.ringCatSheaf U) :=
    moduleOverFunctor_limits X.toRingedSpace U
  let : PreservesFiniteColimits (SheafOfModules.overFunctor X.ringCatSheaf U) :=
    moduleOverFunctor_colimits X.toRingedSpace U
  let : PreservesFiniteLimits r := preservesFiniteLimits_of_natIso (overFunctorEquiv U)
  let : PreservesFiniteColimits r := preservesFiniteColimits_of_natIso (overFunctorEquiv U)
  let : r.Additive := Functor.additive_of_preserves_binary_products r
  let : r.PreservesInjectiveObjects :=
    { injective_obj := fun {M} hM ↦ by
        let : Injective ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M) :=
          (module_open_restriction_injectives X U).2.2.1 M hM
        exact Injective.of_iso ((overFunctorEquiv U).app M)
          ((overEquiv U).functor.injective_obj_of_injective inferInstance) }
  let P := (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let bc := pushforwardRestrictIso (coefficient_restriction_pullback v U)
  let c : rC.obj (((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      J.cocomplex) ≅ P.obj R'.resolution.cocomplex :=
    restrictedRoof_comparison v J U R'
  let lambda : P.obj R'.resolution.cocomplex ⟶ rC.obj L := c.inv ≫ rC.map ell
  let betaU := R.comparison.hom ≫ rC.map beta
  let a := pushforward_sections_iso (v.resLE U (v ⁻¹ᵁ U) le_rfl) R'.resolution.cocomplex
  let ΓU := (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
  let : (restrictFunctor U.ι).Additive := inferInstanceAs r.Additive
  let : (show X.Modules ⥤ AddCommGrpCat.{u} from
      RingedSpace.openModuleSections X.toRingedSpace U).PreservesZeroMorphisms := by
    dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory,
      Scheme.Modules.instAbelian]
    exact Functor.preservesZeroMorphisms_of_additive
      (RingedSpace.openModuleSections X.toRingedSpace U)
  let : (restrictFunctor U.ι ⋙
      RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso (restrictionSectionsIso U).symm
  let cS := NatIso.mapHomologicalComplex (restrictionSectionsIso U) (ComplexShape.up ℕ)
  have hdenom : QuasiIso lambda := by
    let : QuasiIso ell := hell
    dsimp only [lambda]
    infer_instance
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory,
    Scheme.Modules.instAbelian] at *
  have hβ : R.resolution.ι.f 0 ≫ betaU.f 0 =
      restrictedDirectImageMap v φ U ≫
        (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).map (R'.resolution.ι.f 0) ≫
        lambda.f 0 := by
    dsimp only [betaU, lambda, c, restrictedRoof_comparison]
    simp only [HomologicalComplex.comp_f, Iso.trans_inv, Functor.mapIso_inv,
      Iso.symm_inv]
    change R.resolution.ι.f 0 ≫ R.comparison.hom.f 0 ≫ r.map (beta.f 0) =
      restrictedDirectImageMap v φ U ≫
        (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).map (R'.resolution.ι.f 0) ≫
        (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).map (R'.comparison.hom.f 0) ≫
        bc.inv.app (J.cocomplex.X 0) ≫ r.map (ell.f 0)
    rw [← Category.assoc, R.augmentation]
    change r.map (I.ι.f 0) ≫ r.map (beta.f 0) = _
    rw [← r.map_comp, hbeta, r.map_comp, r.map_comp,
      restrictedDirectImageMap_eq]
    simp only [Category.assoc]
    rw [← (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).map_comp_assoc,
      R'.augmentation]
    change r.map φ ≫ r.map ((pushforward v).map (J.ι.f 0)) ≫ r.map (ell.f 0) =
      r.map φ ≫ bc.hom.app G ≫
        (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).map
          ((restrictFunctor (v ⁻¹ᵁ U).ι).map (J.ι.f 0)) ≫
        bc.inv.app (J.cocomplex.X 0) ≫ r.map (ell.f 0)
    have hn : r.map ((pushforward v).map (J.ι.f 0)) ≫ bc.hom.app (J.cocomplex.X 0) =
        bc.hom.app G ≫ (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).map
          ((restrictFunctor (v ⁻¹ᵁ U).ι).map (J.ι.f 0)) :=
      bc.hom.naturality (show G ⟶ J.cocomplex.X 0 from J.ι.f 0)
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
      congrArg (fun z ↦ r.map φ ≫ z ≫ bc.inv.app (J.cocomplex.X 0) ≫ r.map (ell.f 0)) hn
  have hsec : ΓU.map c.hom ≫ a.inv ≫ R'.sections.hom =
      cS.hom.app (((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        J.cocomplex) := restriction_pushforward_sections v J U R'
  have hden : (a.hom ≫ ΓU.map lambda) ≫ cS.hom.app L =
      R'.sections.hom ≫ Γ.map ell :=
    roof_denominator_naturality rC ΓU Γ cS c a R'.sections.hom ell hsec
  have hnum : ΓU.map betaU ≫ cS.hom.app L = R.sections.hom ≫ Γ.map beta := by
    have hn : ΓU.map (rC.map beta) ≫ cS.hom.app L =
        cS.hom.app I.cocomplex ≫ Γ.map beta := cS.hom.naturality beta
    have hc : ΓU.map R.comparison.hom ≫ cS.hom.app I.cocomplex =
        R.sections.hom := by
      apply HomologicalComplex.hom_ext
      intro n
      rw [R.components n]
      dsimp only [cS]
      unfold restrictionSectionsIso
      change Hom.app (R.comparison.hom.f n) ⊤ ≫
        ((restrictAppIso U.ι (I.cocomplex.X n) ⊤).hom ≫
          (I.cocomplex.X n).presheaf.map
            (eqToHom (congrArg op U.ι_image_top))) = _
      simp only [eqToHom_op]
    calc
      _ = ΓU.map R.comparison.hom ≫ (ΓU.map (rC.map beta) ≫ cS.hom.app L) := by
        exact map_comp_post ΓU R.comparison.hom (rC.map beta) (cS.hom.app L)
      _ = ΓU.map R.comparison.hom ≫ (cS.hom.app I.cocomplex ≫ Γ.map beta) :=
        congrArg (fun z ↦ ΓU.map R.comparison.hom ≫ z) hn
      _ = _ := by
        simpa only [Category.assoc] using (congrArg (fun z ↦ z ≫ Γ.map beta) hc)
  let D : ModuleCohomologyFMapData (v.resLE U (v ⁻¹ᵁ U) le_rfl)
      ((restrictFunctor U.ι).obj F) ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G)
      (restrictedDirectImageMap v φ U) := {
    I := R'.resolution
    J := R.resolution
    K := rC.obj L
    injective := fun n ↦ r.injective_obj_of_injective (hL n)
    lambda := lambda
    quasiIso := hdenom
    β := betaU
    compatible := hβ
    a := a
    sections := by intro n; rfl
    invertible := by
      intro p
      have : QuasiIso (ΓU.map lambda) :=
        nat_quasiIso_globalSections_pushforward_injectives _
          R'.resolution.cocomplex (rC.obj L) (fun n ↦ inferInstance)
          (fun n ↦ r.injective_obj_of_injective (hL n)) lambda hdenom
      have : IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
          (ComplexShape.up ℕ) p).map (ΓU.map lambda)) := by
        change IsIso (HomologicalComplex.homologyMap _ p)
        infer_instance
      rw [Functor.map_comp]
      infer_instance }
  have hi : moduleCohomologyFMap (v.resLE U (v ⁻¹ᵁ U) le_rfl)
      (restrictedDirectImageMap v φ U) q = D.map q := by
    unfold moduleCohomologyFMap
    exact moduleCohomologyFMap_independent _ (restrictedDirectImageMap v φ U)
      (Classical.choice (moduleCohomologyFMapData_nonempty _ _ _ _)) D q
  have hD : D.map q ≫ rJ.hom ≫ H.map (a.hom ≫ ΓU.map lambda) =
      rI.hom ≫ H.map (ΓU.map betaU) := coefficientData_roof_formula D q
  let Γ' := (RingedSpace.globalSectionsFunctor (v ⁻¹ᵁ U).toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
  refine (congrArg (fun f ↦ f ≫ rJ.hom ≫ H.map R'.sections.hom ≫ H.map (Γ.map ell))
    hi).trans ?_
  exact roof_transport H
    (I := ΓU.obj R.resolution.cocomplex)
    (J := Γ'.obj R'.resolution.cocomplex)
    (K := ΓU.obj (rC.obj L)) (L := Γ.obj L)
    (M := Γ.obj I.cocomplex)
    (N := Γ.obj (((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex))
    (D.map q) rI.hom rJ.hom
    (a.hom ≫ ΓU.map lambda) (ΓU.map betaU) (cS.hom.app L)
    R.sections.hom R'.sections.hom (Γ.map ell) (Γ.map beta) hD hden hnum

end AlgebraicGeometry
