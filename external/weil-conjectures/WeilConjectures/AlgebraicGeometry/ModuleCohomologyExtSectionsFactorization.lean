/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension

/-! # The Ext-to-abelian-sections part of the comparison

Source: Stacks Project, Tags 015E and 03FD.
(blueprint: new-module-cohomology-ext-sections-factorization)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sectionsComparisonNatIso_apply
    {A E : Type*} [Category A] [Category E]
    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R} {T : A ⥤ E}
    {B L Q : E ⥤ AddCommGrpCat.{u}}
    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ B)
    (b : L ≅ B) (c : L ≅ Q) (F : A) (x : K.obj F) :
    moduleComparisonEquiv (sectionsComparisonNatIso a b c) F x =
      (c.hom.app (T.obj F)) ((b.inv.app (T.obj F)) ((a.hom.app F) x)) := by
  rfl

private theorem moduleComparisonEquiv_apply_of_component
    {A : Type*} [Category A] {R : Type u} [Ring R]
    {K : A ⥤ ModuleCat.{u} R} {L : A ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L) (F : A)
    {B C : AddCommGrpCat.{u}}
    (a : (forget₂ _ AddCommGrpCat.{u}).obj (K.obj F) ≅ B)
    (b : C ≅ B) (c : C ≃+ L.obj F)
    (h : η.app F = a ≪≫ b.symm ≪≫ c.toAddCommGrpIso) (x : K.obj F) :
    moduleComparisonEquiv η F x = c (b.inv (a.hom x)) := by
  change (η.app F).hom x = _
  rw [h]
  rfl

private theorem comparisonNatIso_symm_app
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G) (X : C) :
    e.symm.app X = (e.app X).symm := rfl

private theorem siteSectionsSourceChange_app
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (F : Sheaf J AddCommGrpCat.{u}) (p : ℕ)
    (e : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
        (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) :
    ((siteSectionsNatIso J U p).symm ≪≫ siteExtNatIso J U p ≪≫
      extSourceNatIso e p ≪≫ siteHNatIso J p).app F =
      (siteSectionsObjIso J U F p).symm ≪≫
        (Abelian.Ext.precompAddEquiv e F p).symm.toAddCommGrpIso := by
  simp only [siteExtNatIso, siteHNatIso, Iso.refl_trans, Iso.trans_refl,
    NatIso.trans_app, comparisonNatIso_symm_app, siteSectionsObjIso,
    extSourceNatIso, NatIso.ofComponents.app]

/-- The fixed module-to-Ext comparison factors through abelian derived sections.
Source: Stacks Project, Tags 015E and 03FD; the Ext-to-sections half of the defining
composite in ModuleCohomologyExtResolutionNaturality.
(blueprint: new-module-cohomology-ext-sections-factorization)

Proof: Unfold the fixed comparison and its natural isomorphism. Its constructor
composes the common-resolution section comparison, the inverse site-section
comparison, and the terminal Ext-source comparison. First evaluate this three-map
composite for arbitrary functors, before specializing to the scheme. Apply that
component formula and unfold the definition of module cohomology and the Ext-valued
cohomology type. The inverse site component is siteSectionsObjIso.inv, and the
terminal component is precompAddEquiv.symm. Their composite gives the asserted
formula. This never unfolds the acyclic-resolution comparison inside the first
factor, and includes degree zero, zero coefficients and empty schemes. -/
theorem ext_sections_factorization
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (p : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    moduleCohomologyExtResolutionEquiv X F p x = (by
      letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
        (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
      let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
      let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
      let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
      let V := forget₂ (ModuleCat.{u}
        ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
      let d := siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ (T.obj F) p
      exact (Abelian.Ext.precompAddEquiv (terminalSourceIso X) (T.obj F) p).symm
        (d.inv (((resolutionSectionsNatIso G V T Γ p (sectionHomologyIso X p)
          (fun M _ ↦ forgottenInjectiveAcyclic X M)).app F).hom x))) := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  -- Compare natural isomorphisms before evaluating their components.
  unfold moduleCohomologyExtResolutionEquiv
  let a := resolutionSectionsNatIso
    (A := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (B := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    (D := AddCommGrpCat.{u})
    (E := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    G V T Γ p (sectionHomologyIso X p)
    (fun M _ ↦ forgottenInjectiveAcyclic X M)
  let b := siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ (T.obj F) p
  let c := Abelian.Ext.precompAddEquiv (terminalSourceIso X) (T.obj F) p
  have hη : moduleCohomologyExtResolutionNatIso X p = a ≪≫ Functor.isoWhiskerLeft T
      ((siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ p).symm ≪≫
        siteExtNatIso (Opens.grothendieckTopology X) ⊤ p ≪≫
          extSourceNatIso (terminalSourceIso X) p ≪≫
            siteHNatIso (Opens.grothendieckTopology X) p) := by
    unfold moduleCohomologyExtResolutionNatIso
    rfl
  have hcomp : (moduleCohomologyExtResolutionNatIso X p).app F =
      a.app F ≪≫ b.symm ≪≫ c.symm.toAddCommGrpIso := by
    rw [hη, NatIso.trans_app]
    apply congrArg (fun e ↦ a.app F ≪≫ e)
    change ((siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ p).symm ≪≫
      siteExtNatIso (Opens.grothendieckTopology X) ⊤ p ≪≫
        extSourceNatIso (terminalSourceIso X) p ≪≫
          siteHNatIso (Opens.grothendieckTopology X) p).app (T.obj F) = _
    exact siteSectionsSourceChange_app (Opens.grothendieckTopology X) ⊤ (T.obj F) p
      (terminalSourceIso X)
  have h := moduleComparisonEquiv_apply_of_component
    (moduleCohomologyExtResolutionNatIso X p) F (a.app F) b c.symm hcomp x
  dsimp only [id, Functor.comp_obj, RingedSpace.moduleCohomology,
    AlgebraicGeometry.Scheme.Modules.H, AlgebraicGeometry.Scheme.Modules.instAddCommGroupH,
    Sheaf.functorH, Sheaf.H, Sheaf.H'] at h ⊢
  -- Align the comparison objects before projecting their maps; otherwise instance conversion
  -- unfolds the derived functor constructions underneath those projections.
  conv_rhs =>
    pattern resolutionSectionsNatIso _ _ _ _ _ _ _
    change a
  conv_rhs =>
    pattern siteSectionsObjIso _ _ _ _
    change b
  conv_rhs =>
    pattern Abelian.Ext.precompAddEquiv _ _ _
    change c
  exact h

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
