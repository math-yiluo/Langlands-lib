import Langlands.Cohomology.EquivariantComposite.AcyclicHomology
import Langlands.Cohomology.DerivedPlusSource
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCompositionProof
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Comparison of derived sections with derived Hom -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.Cohomology.DerivedSectionsHomComparison

universe w wC wD v vD uC uA uD

variable {C : Type uC} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{wC} C]
  {A : Type uA} [Category.{v} A] [Abelian A] [HasDerivedCategory.{max v w} A]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive]
  (G : D ⥤ AddCommGrpCat.{v}) [G.Additive] [G.PreservesHomology]
  (U : C ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (Z : A)
  (e : F ⋙ G ≅ U ⋙ preadditiveCoyoneda.obj (op Z))

/-- The termwise sections/Hom identification on integer complexes. -/
def sectionsComplexIso (K : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅
      ((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).obj
        ((U.mapHomologicalComplex (.up ℤ)).obj K) :=
  (Functor.mapHomologicalComplexCompIso e (.up ℤ)).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (U ⋙ preadditiveCoyoneda.obj (op Z))) (.up ℤ)).app K).symm

/-- Homology of localized sections, with an exact change of target category. -/
abbrev sectionsCohomology (n : ℤ) :
    DerivedCategory.Plus D ⥤ AddCommGrpCat.{max v w} :=
  DerivedCategory.Plus.homologyFunctor D n ⋙ G ⋙ AddCommGrpCat.uliftFunctor.{w, v}

/-- The underived sections cohomology is cohomology of termwise Hom. -/
def sectionsHomologyIso (K : CochainComplex.Plus C) (n : ℤ) :
    G.obj ((DerivedCategory.Plus.homologyFunctor D n).obj
      (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K))) ≅
      (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).obj
        ((U.mapHomologicalComplex (.up ℤ)).obj K.obj)).homology n :=
  G.mapIso (DerivedPlusSource.localizedHomologyIso (F.mapCochainComplexPlus.obj K) n) ≪≫
    ((((F.mapHomologicalComplex (.up ℤ)).obj K.obj).sc n).mapHomologyIso G).symm ≪≫
    HomologicalComplex.homologyMapIso (sectionsComplexIso F G U Z e K.obj) n

omit [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory A]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
@[reassoc]
lemma sectionsHomologyIso_hom_naturality
    {K L : CochainComplex.Plus C} (a : K ⟶ L) (n : ℤ) :
    G.map ((DerivedCategory.Plus.homologyFunctor D n).map
        (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map a))) ≫
      (sectionsHomologyIso F G U Z e L n).hom =
    (sectionsHomologyIso F G U Z e K n).hom ≫
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).map
          ((U.mapHomologicalComplex (.up ℤ)).map a.hom)) n := by
  have h₁ := congrArg G.map
    (DerivedPlusSource.localizedHomologyIso_hom_naturality
      (F.mapCochainComplexPlus.map a) n)
  have h₂ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor D (.up ℤ) n).map
      ((F.mapHomologicalComplex (.up ℤ)).map a.hom)) G
  have h₃ : (G.mapHomologicalComplex (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map a.hom) ≫
        (sectionsComplexIso F G U Z e L.obj).hom =
      (sectionsComplexIso F G U Z e K.obj).hom ≫
        ((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).map
          ((U.mapHomologicalComplex (.up ℤ)).map a.hom) := by
    apply HomologicalComplex.hom_ext
    intro i
    exact e.hom.naturality (a.hom.f i)
  change G.map (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map a.hom) n) ≫
        ((((F.mapHomologicalComplex (.up ℤ)).obj L.obj).sc n).mapHomologyIso G).inv =
      ((((F.mapHomologicalComplex (.up ℤ)).obj K.obj).sc n).mapHomologyIso G).inv ≫
        HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (.up ℤ)).map
            ((F.mapHomologicalComplex (.up ℤ)).map a.hom)) n at h₂
  have h₄ := congrArg (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map h₃
  simp only [Functor.map_comp] at h₁ h₄
  simp only [sectionsHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  erw [reassoc_of% h₁, reassoc_of% h₂, h₄]
  rfl

/-- Derived Hom from `Z` on the exact image of a derived module complex. -/
abbrev derivedHom (n : ℤ) : DerivedCategory.Plus C ⥤ AddCommGrpCat.{max v w} :=
  DerivedCategory.Plus.ι ⋙ U.mapDerivedCategory ⋙
    CategoryTheory.shiftFunctor (DerivedCategory A) n ⋙
      preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj Z))

/-- The same Hom functor on actual complexes. -/
abbrev complexHom (n : ℤ) : CochainComplex.Plus C ⥤ AddCommGrpCat.{max v w} :=
  U.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι A ⋙ DerivedCategory.Q ⋙
    CategoryTheory.shiftFunctor (DerivedCategory A) n ⋙
      preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj Z))

/-- Exactness identifies the derived-Hom model with its complex model. -/
def derivedHomFactors (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ derivedHom U Z n ≅ complexHom U Z n :=
  NatIso.ofComponents (fun K =>
    (CategoryTheory.shiftFunctor (DerivedCategory A) n ⋙
      preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj Z))).mapIso
      (U.mapDerivedCategory.mapIso ((DerivedCategory.Plus.QCompιIso C).app K) ≪≫
        U.mapDerivedCategoryFactors.app K.obj))
    (fun a => by
      dsimp
      simp only [← Functor.map_comp]
      congr 1
      congr 1
      have h₁ := (DerivedCategory.Plus.QCompιIso C).hom.naturality a
      have h₂ := U.mapDerivedCategoryFactors.hom.naturality a.hom
      simp only [Functor.comp_map] at h₁ h₂
      erw [← U.mapDerivedCategory.map_comp_assoc, h₁,
        U.mapDerivedCategory.map_comp, Category.assoc, h₂]
      rw [Category.assoc]
      rfl)

/-- The canonical cycle-localization map on section cohomology. -/
def complexComparison (n : ℤ) :
    F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ sectionsCohomology G n ⟶
      complexHom U Z n where
  app K := AddCommGrpCat.ofHom
    ((EquivariantComposite.homologyDerivedMap Z
      ((U.mapHomologicalComplex (.up ℤ)).obj K.obj) n).comp
      ((sectionsHomologyIso F G U Z e K n).hom.hom.comp
        AddEquiv.ulift.toAddMonoidHom))
  naturality K L a := by
    ext x
    have h := ConcreteCategory.congr_hom
      (sectionsHomologyIso_hom_naturality F G U Z e a n) x.down
    change EquivariantComposite.homologyDerivedMap Z _ n
      ((sectionsHomologyIso F G U Z e L n).hom
        (G.map ((DerivedCategory.Plus.homologyFunctor D n).map
          (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map a))) x.down)) = _
    change (sectionsHomologyIso F G U Z e L n).hom
      (G.map ((DerivedCategory.Plus.homologyFunctor D n).map
        (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map a))) x.down) = _ at h
    rw [h]
    exact EquivariantComposite.homologyDerivedMap_naturality Z
      ((U.mapHomologicalComplex (.up ℤ)).map a.hom) n _

/-- Cohomology of derived sections. -/
abbrev derivedSections (n : ℤ) :
    DerivedCategory.Plus C ⥤ AddCommGrpCat.{max v w} :=
  F.rightDerivedFunctorPlus ⋙ sectionsCohomology G n

/-- The sections unit followed by cohomology and exact scalar forgetting. -/
abbrev sectionsUnit (n : ℤ) :
    F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ sectionsCohomology G n ⟶
      DerivedCategory.Plus.Q ⋙ derivedSections F G n :=
  Functor.whiskerRight F.rightDerivedFunctorPlusUnit (sectionsCohomology G n)

instance derivedSections_isRightDerivedFunctor (n : ℤ) :
    (derivedSections F G n).IsRightDerivedFunctor (sectionsUnit F G n)
      (CochainComplex.Plus.quasiIso C) := by
  let Φ := CochainComplex.Plus.localizerMorphism C
  have hT : Φ.Derives
      (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ sectionsCohomology G n) :=
    MorphismProperty.IsInvertedBy.of_comp _
      (Φ.functor ⋙ F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q)
      (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus F)
      (sectionsCohomology G n)
  apply hT.isRightDerivedFunctor_of_isIso
  intro K
  dsimp [sectionsUnit, Φ]
  infer_instance

/-- The natural comparison induced by the canonical cycle-localization map. -/
def comparison (n : ℤ) :
    derivedSections F G n ⟶ derivedHom U Z n :=
  Functor.rightDerivedDesc (derivedSections F G n) (sectionsUnit F G n)
    (CochainComplex.Plus.quasiIso C) (derivedHom U Z n)
    (complexComparison F G U Z e n ≫ (derivedHomFactors U Z n).inv)

/-- The derived comparison expressed on actual bounded below complexes. -/
def comparisonOnComplex (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ derivedSections F G n ⟶ complexHom U Z n :=
  Functor.whiskerLeft DerivedCategory.Plus.Q (comparison F G U Z e n) ≫
    (derivedHomFactors U Z n).hom

@[reassoc]
lemma unit_comparisonOnComplex (n : ℤ) :
    sectionsUnit F G n ≫ comparisonOnComplex F G U Z e n =
      complexComparison F G U Z e n := by
  dsimp only [comparisonOnComplex, comparison]
  rw [← Category.assoc, Functor.rightDerived_fac]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
lemma unit_comparisonOnComplex_app (K : CochainComplex.Plus C) (n : ℤ) :
    (sectionsUnit F G n).app K ≫ (comparisonOnComplex F G U Z e n).app K =
      (complexComparison F G U Z e n).app K :=
  NatTrans.congr_app (unit_comparisonOnComplex F G U Z e n) K

section Acyclic

variable [EnoughInjectives A]
  (hU : ∀ (I : InjectiveObject C) (q : ℕ), IsZero
    (((preadditiveCoyoneda.obj (op Z)).rightDerived (q + 1)).obj (U.obj I.obj)))

include hU in
omit [EnoughInjectives C] [HasDerivedCategory C]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
lemma isIso_complexComparison_on_injectives
    (K : CochainComplex.Plus (InjectiveObject C)) (n : ℤ) :
    IsIso ((complexComparison F G U Z e n).app
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj K)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact (EquivariantComposite.homologyDerivedMap_bijective Z
      (U.mapCochainComplexPlus.obj
        ((InjectiveObject.ι C).mapCochainComplexPlus.obj K))
      (fun i q => hU (K.obj.X i) q) n).comp
    ((sectionsHomologyIso F G U Z e
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj K) n).addCommGroupIsoToAddEquiv.bijective.comp
        AddEquiv.ulift.bijective)

include hU in
lemma isIso_comparison (n : ℤ) :
    IsIso (comparison F G U Z e n) := by
  let Φ := CochainComplex.Plus.localizerMorphism C
  have h (K : CochainComplex.Plus (InjectiveObject C)) :
      IsIso ((comparison F G U Z e n).app
        (DerivedCategory.Plus.Q.obj (Φ.functor.obj K))) := by
    have : IsIso ((sectionsUnit F G n).app (Φ.functor.obj K)) := by
      dsimp [sectionsUnit, Φ]
      infer_instance
    have := isIso_complexComparison_on_injectives F G U Z e hU K n
    rw [← isIso_comp_left_iff ((sectionsUnit F G n).app (Φ.functor.obj K))]
    rw [← isIso_comp_right_iff _ ((derivedHomFactors U Z n).hom.app (Φ.functor.obj K))]
    rw [Category.assoc]
    change IsIso ((sectionsUnit F G n).app (Φ.functor.obj K) ≫
      (comparisonOnComplex F G U Z e n).app (Φ.functor.obj K))
    rw [unit_comparisonOnComplex_app]
    exact this
  have := Φ.essSurj_of_hasRightResolutions (DerivedCategory.Plus.Q (C := C))
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  rw [NatTrans.isIso_app_iff_of_iso (comparison F G U Z e n)
    ((Φ.functor ⋙ DerivedCategory.Plus.Q).objObjPreimageIso Y).symm]
  exact h _

end Acyclic

end Langlands.Cohomology.DerivedSectionsHomComparison
