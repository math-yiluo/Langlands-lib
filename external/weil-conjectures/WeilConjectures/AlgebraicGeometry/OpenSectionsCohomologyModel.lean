/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Ordinary representatives for the open-sections comparison

Source: Stacks Project, Tags 08BS and 079V.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical abelian structure on ringed-space modules, cached for elaboration.
This is an abbreviation of Mathlib's sheaf-module abelian instance.
(blueprint: lem-sc-open-sections-cohomology-model-comparison). -/
abbrev openComparisonModuleAbelian (X : RingedSpace.{u}) :
    Abelian (SheafOfModules.{u} (moduleRings X)) := inferInstance

/-- The canonical abelian structure on over-site modules, cached for elaboration.
This is an abbreviation of Mathlib's sheaf-module abelian instance.
(blueprint: lem-sc-open-sections-cohomology-model-comparison). -/
abbrev openComparisonOverModuleAbelian (X : RingedSpace.{u})
    (V : TopologicalSpace.Opens X) :
    Abelian (SheafOfModules.{u} ((moduleRings X).over V)) := inferInstance

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

/-- Restriction to the open subscheme, through the over-site equivalence. -/
abbrev openComparisonRestriction (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) :=
  (SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)

/-- Ordinary global sections on the restriction are ordinary sections on the open.
The map is restrictAppIso at the top open composed with overFunctorEquiv. -/
def openComparisonSectionsIso (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) :
    openComparisonRestriction A U ⋙
        RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat ≅
      affineOpenSections A U ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat := by
  let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
    forget₂ (ModuleCat.{u}
      ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  refine Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) S ≪≫ ?_
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · change Γ(Scheme.Modules.restrict M U.ι, ⊤) ≅ Γ(M, U)
    exact (Scheme.Modules.restrictAppIso U.ι M ⊤) ≪≫
      ((Scheme.Modules.toPresheaf (Spec (.of A))).obj M).mapIso
        (eqToIso (by simp : U = U.ι ''ᵁ ⊤)).op
  · intro M N g
    change ((Scheme.Modules.toPresheaf (Spec (.of A))).map g).app
        (op (U.ι ''ᵁ ⊤)) ≫
          ((Scheme.Modules.toPresheaf (Spec (.of A))).obj N).map
            (eqToHom (by simp : U = U.ι ''ᵁ ⊤)).op =
      ((Scheme.Modules.toPresheaf (Spec (.of A))).obj M).map
          (eqToHom (by simp : U = U.ι ''ᵁ ⊤)).op ≫
        ((Scheme.Modules.toPresheaf (Spec (.of A))).map g).app (op U)
    exact ((Scheme.Modules.toPresheaf (Spec (.of A))).map g).naturality _ |>.symm

variable (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens)
  [HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
  [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
  [HasDerivedCategory.{v} (ModuleCat.{u} A)]

/-- Zeroth derived global sections on the open, with its scalars forgotten. -/
def openComparisonGlobalCohomology :
    schemeDerivedCategory U.toScheme ⥤ AddCommGrpCat.{u} := by
  letI := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)))
  exact (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤))) 0 ⋙
    forget₂ (ModuleCat.{u}
      ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat

/-- Zeroth derived sections on the ambient affine scheme, with scalars forgotten. -/
def openComparisonAmbientCohomology : schemeDerivedCategory (Spec (.of A)) ⥤
    AddCommGrpCat.{u} :=
  (affineOpenSections A U).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ⋙
    forget₂ (ModuleCat.{u} A) AddCommGrpCat

/-- The ordinary-to-derived comparison on complexes, with quotient comparisons inserted. -/
def openComparisonComplexUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C] (T : C ⥤ D) [T.Additive] :
    T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ T.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (T.mapHomologicalComplex (.up ℤ))
    (DerivedCategory.quotientCompQhIso D)).inv ≫
  Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) T.rightDerivedFunctorUnit ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) T.rightDerivedFunctor).hom

/-- Ordinary cohomology of ambient open sections, viewed as an additive group. -/
def openComparisonOrdinaryCohomology
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat).obj
    ((((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj K).homology 0)

/-- The ambient ordinary-to-derived cohomology map. -/
def openComparisonAmbientUnit
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    openComparisonOrdinaryCohomology A U K ⟶
      (openComparisonAmbientCohomology A U).obj (DerivedCategory.Q.obj K) :=
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat).map
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app
      (((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((openComparisonComplexUnit (affineOpenSections A U)).app K))

/-- The sections isomorphism on ordinary cohomology, using exact scalar forgetting. -/
def openComparisonOrdinaryIso
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    let J := ((openComparisonRestriction A U).mapHomologicalComplex (.up ℤ)).obj K
    let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat).obj
        ((((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).mapHomologicalComplex
          (.up ℤ)).obj J).homology 0) ≅
      openComparisonOrdinaryCohomology A U K := by
  let J := ((openComparisonRestriction A U).mapHomologicalComplex (.up ℤ)).obj K
  let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
  let S := ((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).mapHomologicalComplex
    (.up ℤ)).obj J
  let T := ((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj K
  let P := forget₂ (ModuleCat.{u} B) AddCommGrpCat
  let Q := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let e : (P.mapHomologicalComplex (.up ℤ)).obj S ≅
      (Q.mapHomologicalComplex (.up ℤ)).obj T :=
    (NatIso.mapHomologicalComplex (openComparisonSectionsIso A U) (.up ℤ)).app K
  exact ((S.sc 0).mapHomologyIso P).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).mapIso e ≪≫
    (T.sc 0).mapHomologyIso Q

/-- The same ordinary class mapped to derived sections of the restricted complex. -/
def openComparisonRestrictedUnit
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    openComparisonOrdinaryCohomology A U K ⟶
      (openComparisonGlobalCohomology A U).obj
        ((openComparisonRestriction A U).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) := by
  let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
  letI := HasDerivedCategory.standard (ModuleCat.{u} B)
  let T := openComparisonRestriction A U
  let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let J := (T.mapHomologicalComplex (.up ℤ)).obj K
  let V := (S.mapHomologicalComplex (.up ℤ)).obj J
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let P := forget₂ (ModuleCat.{u} B) AddCommGrpCat
  exact (openComparisonOrdinaryIso A U K).inv ≫
    P.map (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) 0).app V).inv ≫
      H.map ((openComparisonComplexUnit S).app J)) ≫
    (openComparisonGlobalCohomology A U).map (T.mapDerivedCategoryFactors.inv.app K)

private def ordinaryDerivedUnit
    {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (P : D ⥤ E) :
    F.mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (.up ℤ) 0 ⋙ P ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D 0 ⋙ P :=
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (Functor.whiskerRight (DerivedCategory.homologyFunctorFactors D 0).inv P) ≫
    Functor.whiskerRight (openComparisonComplexUnit F)
      (DerivedCategory.homologyFunctor D 0 ⋙ P)

private theorem ordinaryDerivedUnit_isIso
    {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (P : D ⥤ E)
    (K : CochainComplex C ℤ) [K.IsKInjective] :
    IsIso ((ordinaryDerivedUnit F P).app K) := by
  dsimp [ordinaryDerivedUnit, openComparisonComplexUnit]
  infer_instance

private theorem ordinaryCohomology_derives
    {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (P : D ⥤ E) :
    (CochainComplex.KInjectives.localizerMorphism C).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (.up ℤ) 0 ⋙ P) := by
  intro K L f hf
  have : K.obj.IsKInjective := K.property
  have : L.obj.IsKInjective := L.property
  have hq : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
  have he' : QuasiIso
      ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (P.map (HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (.up ℤ)).map f.hom) 0))
  infer_instance

private theorem mapHomologicalComplexHomologyIso_app
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (P : C ⥤ D) [P.Additive] [P.PreservesHomology] (K : CochainComplex C ℤ) :
    (P.mapHomologicalComplexHomologyIso (.up ℤ) 0).app K = (K.sc 0).mapHomologyIso P := by
  apply Iso.ext
  simp only [Functor.comp_obj, Functor.mapHomologicalComplexHomologyIso,
    HomologicalComplex.homologyFunctorIso, Functor.isoWhiskerLeft_refl,
    Functor.mapHomologicalComplexCompShortComplexFunctorIso, Functor.isoWhiskerRight_refl,
    ShortComplex.homologyFunctorIso, Iso.refl_symm, Iso.refl_trans, NatIso.trans_app,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    NatIso.ofComponents_hom_app, Functor.isoWhiskerRight_hom, Iso.refl_hom,
    Functor.whiskerRight_app, NatTrans.id_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, Category.id_comp]

private theorem over_preservesKInjective (X : RingedSpace.{u})
    (V : TopologicalSpace.Opens X) :
    (SheafOfModules.overFunctor.{u} (moduleRings X) V).PreservesKInjectiveComplexes := by
  obtain ⟨h₁, h₂, h₃, h₄, ⟨adj⟩⟩ := open_restriction_adjunction_exact X V
  let L := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
    PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)
  have : PreservesFiniteLimits L := h₃
  have : PreservesFiniteColimits L := h₄
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  exact adj.preservesKInjectiveComplexes

-- Keep the existing over-site parameter even though the proof needs no derived over-site.
set_option linter.unusedSectionVars false in
-- Inline the standard module-derived category to match the comparison map's data.
set_option linter.style.haveILetI false in
-- The normalized comparison checks several concrete functor identifications.
/-- The open-sections comparison is normalized on every ordinary complex class.
Source: Stacks Project, Tags 08BS and 079V.
(blueprint: lem-sc-open-sections-cohomology-model-comparison).

Proof: Let T be restriction through the over-equivalence. Extension by zero is an exact
left adjoint of over-restriction, so the adjunction criterion for preservation of
K-injectives applies. The over-equivalence also preserves K-injectives. Thus T sends
K-injectives to K-injectives. On a K-injective representative J the ordinary-to-derived
units for ambient sections and for global sections on T(J) are isomorphisms.
The exact scalar-forgetting functors commute with homology. Conjugate the ordinary
sections isomorphism openComparisonOrdinaryIso by these two units and by the exact
restriction factorization to obtain the comparison at Q(J). Naturality of all four
maps proves naturality for homotopy classes of chain maps. Localization is fully
faithful on K-injectives, and every derived object has such a representative, so this
comparison descends to a natural isomorphism on the specified ambient derived category.
For an arbitrary complex K choose a quasi-isomorphism K to J. Naturality of both units
and of the sections and homology comparisons proves the displayed square after mapping
to J. Since the induced derived map is invertible, cancel it to obtain the square on K.
No quasi-coherence or boundedness is required; an empty open and the zero ring give
zero groups with the same comparison. The two module-derived categories may have
different universe choices: all conjugations occur through their own units and Q.
-/
theorem exists_openComparison_cohomology_model_iso :
    ∃ e : (openComparisonRestriction A U).mapDerivedCategory ⋙
        openComparisonGlobalCohomology A U ≅ openComparisonAmbientCohomology A U,
      ∀ (K : CochainComplex
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ),
        openComparisonRestrictedUnit A U K ≫ e.hom.app (DerivedCategory.Q.obj K) =
          openComparisonAmbientUnit A U K := by
  let C := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  letI : Abelian C := inferInstance
  letI : Abelian D := inferInstance
  let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
  letI := HasDerivedCategory.standard (ModuleCat.{u} B)
  let T := openComparisonRestriction A U
  have hTa : T.Additive := inferInstance
  have hTz : T.PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ T hTa
  have hTl : PreservesFiniteLimits T := inferInstance
  have hTc : PreservesFiniteColimits T := inferInstance
  let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let P := forget₂ (ModuleCat.{u} B) AddCommGrpCat
  let R := affineOpenSections A U
  let Q := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let O := R.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) 0 ⋙ Q
  let F := T.mapDerivedCategory ⋙ openComparisonGlobalCohomology A U
  let G := openComparisonAmbientCohomology A U
  let oi : T.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0 ⋙ P ≅ O :=
    Functor.isoWhiskerLeft
        (T.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ))
        (P.mapHomologicalComplexHomologyIso (.up ℤ) 0).symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (openComparisonSectionsIso A U) (.up ℤ))
        (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0) ≪≫
      Functor.isoWhiskerLeft (R.mapHomologicalComplex (.up ℤ))
        (Q.mapHomologicalComplexHomologyIso (.up ℤ) 0)
  let α : O ⟶ DerivedCategory.Q ⋙ F :=
    oi.inv ≫
      Functor.whiskerLeft (T.mapHomologicalComplex (.up ℤ)) (ordinaryDerivedUnit S P) ≫
      Functor.whiskerRight T.mapDerivedCategoryFactors.inv
        (openComparisonGlobalCohomology A U)
  let β : O ⟶ DerivedCategory.Q ⋙ G := ordinaryDerivedUnit R Q
  have hoi (K : CochainComplex C ℤ) : oi.app K = openComparisonOrdinaryIso A U K := by
    apply Iso.ext
    simp only [oi, NatIso.trans_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_hom, Functor.comp_obj, Iso.app_hom]
    simp only [← Iso.app_inv, ← Iso.app_hom, mapHomologicalComplexHomologyIso_app]
    rfl
  have hα (K : CochainComplex C ℤ) :
      α.app K = openComparisonRestrictedUnit A U K := by
    simp only [α, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [← Iso.app_inv, hoi]
    simp only [ordinaryDerivedUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_map]
    rw [← P.map_comp]
    rfl
  have hβ (K : CochainComplex C ℤ) :
      β.app K = openComparisonAmbientUnit A U K := by
    change Q.map _ ≫ Q.map _ = Q.map (_ ≫ _)
    exact (Q.map_comp _ _).symm
  have hder := ordinaryCohomology_derives R Q
  have hT : T.PreservesKInjectiveComplexes := by
    let T₀ := SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U
    let E := (Scheme.Modules.overEquiv U).functor
    have : T₀.PreservesKInjectiveComplexes :=
      over_preservesKInjective (Spec (.of A)).toRingedSpace U
    exact Functor.preservesKInjectiveComplexes_comp T₀ E
  have hF : F.IsRightDerivedFunctor α (HomologicalComplex.quasiIso C (.up ℤ)) := by
    apply hder.isRightDerivedFunctor_of_isIso
    intro K
    have : K.obj.IsKInjective := K.property
    have := hT
    have hunit := ordinaryDerivedUnit_isIso S P
      ((T.mapHomologicalComplex (.up ℤ)).obj K.obj)
    dsimp only [α, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    have hunit' : IsIso ((ordinaryDerivedUnit S P).app
        ((T.mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.KInjectives.localizerMorphism C).functor.obj K))) := hunit
    infer_instance
  have hG : G.IsRightDerivedFunctor β (HomologicalComplex.quasiIso C (.up ℤ)) := by
    apply hder.isRightDerivedFunctor_of_isIso
    intro K
    have : K.obj.IsKInjective := K.property
    exact ordinaryDerivedUnit_isIso R Q K.obj
  let e := Functor.rightDerivedUnique F G α β (HomologicalComplex.quasiIso C (.up ℤ))
  refine ⟨e, fun K ↦ ?_⟩
  have he : α.app K ≫ e.hom.app (DerivedCategory.Q.obj K) = β.app K := by
    dsimp only [e, Functor.rightDerivedUnique, Functor.rightDerivedNatIso]
    simpa only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app F G α β
        (HomologicalComplex.quasiIso C (.up ℤ)) (Iso.refl O).hom K
  rw [hα K, hβ K] at he
  exact he

end
end AlgebraicGeometry
