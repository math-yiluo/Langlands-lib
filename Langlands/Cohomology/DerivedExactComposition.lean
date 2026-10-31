import Langlands.Cohomology.DerivedExactPostcomposition
import Langlands.Cohomology.DerivedComparison

/-!
# Derived complexes of exact composites

A natural isomorphism of additive functors induces a natural isomorphism of
their actual derived complexes, and an exact functor applied to the derived
complex of `G` agrees with the derived complex of any functor isomorphic to
the composite. Cohomology of the induced functor on derived categories is the
image of cohomology under the exact functor.
-/

noncomputable section

namespace Langlands.Cohomology.DerivedPlus

open CategoryTheory CategoryTheory.Limits
open AcyclicResolution

universe wC wD wE vC vD vE vF uC uD uE uF

section Congr

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {G H : C ⥤ D} [G.Additive] [H.Additive] (e : G ≅ H)

/-- A natural isomorphism of additive functors on the localized image of an
arbitrary natural-indexed complex. -/
def resolutionCongrNatIso :
    derivedResolutionFunctor G ≅ derivedResolutionFunctor H :=
  Functor.isoWhiskerLeft (ComplexShape.embeddingUpNat.extendFunctor C)
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The isomorphism of derived complexes induced by `e`, computed with a
specified injective resolution. -/
def derivedComplexCongrOfResolution {X : C} (I : InjectiveResolution X) :
    (derivedComplex G ⋙ DerivedCategory.Plus.ι).obj X ≅
      (derivedComplex H ⋙ DerivedCategory.Plus.ι).obj X :=
  derivedResolutionIso G I ≪≫ (resolutionCongrNatIso e).app I.cocomplex ≪≫
    (derivedResolutionIso H I).symm

set_option backward.isDefEq.respectTransparency false in
/-- The resolution formula commutes with every morphism of injective
resolutions over a coefficient morphism. -/
@[reassoc]
theorem derivedComplexCongrOfResolution_hom_naturality
    {X Y : C} {f : X ⟶ Y} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) :
    (derivedComplex G ⋙ DerivedCategory.Plus.ι).map f ≫
        (derivedComplexCongrOfResolution e J).hom =
      (derivedComplexCongrOfResolution e I).hom ≫
        (derivedComplex H ⋙ DerivedCategory.Plus.ι).map f := by
  have h₁ := derivedResolutionIso_hom_naturality G φ
  have h₂ := (resolutionCongrNatIso e).hom.naturality φ.hom
  have h₃ := derivedResolutionIso_hom_naturality H φ
  have h₃' :
      (derivedResolutionFunctor H).map φ.hom ≫ (derivedResolutionIso H J).inv =
        (derivedResolutionIso H I).inv ≫
          (derivedComplex H ⋙ DerivedCategory.Plus.ι).map f := by
    rw [← cancel_mono (derivedResolutionIso H J).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h₃, Iso.inv_hom_id_assoc]
  simp only [derivedComplexCongrOfResolution, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Category.assoc]
  rw [← Category.assoc, h₁, Category.assoc,
    ← Category.assoc ((derivedResolutionFunctor G).map φ.hom), h₂, Category.assoc, h₃']

/-- The isomorphism is independent of the injective resolution used to
compute it. -/
theorem derivedComplexCongrOfResolution_hom_eq {X : C} (I J : InjectiveResolution X) :
    (derivedComplexCongrOfResolution e I).hom = (derivedComplexCongrOfResolution e J).hom := by
  have h := derivedComplexCongrOfResolution_hom_naturality e (descHom (𝟙 X) I J)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id] at h
  exact h.symm

/-- A natural isomorphism of additive functors induces a natural isomorphism of
their actual derived complexes in the unbounded derived category. -/
def derivedComplexCongr :
    derivedComplex G ⋙ DerivedCategory.Plus.ι ≅ derivedComplex H ⋙ DerivedCategory.Plus.ι :=
  NatIso.ofComponents
    (fun X => derivedComplexCongrOfResolution e (injectiveResolution X))
    (fun f => derivedComplexCongrOfResolution_hom_naturality e (descHom f _ _))

/-- Every injective resolution computes the component of `derivedComplexCongr`. -/
theorem derivedComplexCongr_hom_app {X : C} (I : InjectiveResolution X) :
    (derivedComplexCongr e).hom.app X = (derivedComplexCongrOfResolution e I).hom :=
  derivedComplexCongrOfResolution_hom_eq e _ I

/-- In either injective-resolution model, `derivedComplexCongr` is the termwise
isomorphism induced by `e`. -/
@[reassoc]
theorem derivedComplexCongr_hom_resolution {X : C} (I : InjectiveResolution X) :
    (derivedComplexCongr e).hom.app X ≫ (derivedResolutionIso H I).hom =
      (derivedResolutionIso G I).hom ≫ (resolutionCongrNatIso e).hom.app I.cocomplex := by
  rw [derivedComplexCongr_hom_app e I]
  simp only [derivedComplexCongrOfResolution, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Congr

section Comp

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  (G : C ⥤ D) [G.Additive] (P : D ⥤ E) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {H : C ⥤ E} [H.Additive] (e : G ⋙ P ≅ H)

/-- An exact functor applied to the actual derived complex of `G` is naturally
the actual derived complex of any additive functor `H` isomorphic to `G ⋙ P`. -/
def derivedCompIso :
    (derivedComplex G ⋙ DerivedCategory.Plus.ι) ⋙ P.mapDerivedCategory ≅
      derivedComplex H ⋙ DerivedCategory.Plus.ι :=
  derivedPostcompIso G P ≪≫ derivedComplexCongr e

/-- In the injective-resolution models, `derivedCompIso` is exact
postcomposition followed by the termwise isomorphism induced by `e`. -/
@[reassoc]
theorem derivedCompIso_hom_resolution {X : C} (I : InjectiveResolution X) :
    (derivedCompIso G P e).hom.app X ≫ (derivedResolutionIso H I).hom =
      P.mapDerivedCategory.map (derivedResolutionIso G I).hom ≫
        (resolutionPostcompNatIso G P).hom.app I.cocomplex ≫
        (resolutionCongrNatIso e).hom.app I.cocomplex := by
  simp only [derivedCompIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    derivedComplexCongr_hom_resolution, derivedPostcompIso_hom_resolution_assoc]

end Comp

section Homology

variable {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  (P : D ⥤ E) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- Homology of the termwise image of a homological complex under an exact
functor is the image of its homology. -/
def mapHomologicalComplexHomologyIso {ι : Type*} (c : ComplexShape ι) (i : ι) :
    P.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor E c i ≅
      HomologicalComplex.homologyFunctor D c i ⋙ P :=
  NatIso.ofComponents (fun K => (K.sc i).mapHomologyIso P)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor D c i).map f) P)

@[simp]
lemma mapHomologicalComplexHomologyIso_hom_app {ι : Type*} (c : ComplexShape ι) (i : ι)
    (K : HomologicalComplex D c) :
    (mapHomologicalComplexHomologyIso P c i).hom.app K = ((K.sc i).mapHomologyIso P).hom :=
  rfl

variable [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wE} E] (n : ℤ)

/-- The source of `mapDerivedCategoryHomologyIso` lifts termwise image
followed by homology. -/
instance mapDerivedCategoryHomologyLifting :
    Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℤ) n)
      (P.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor E n) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight P.mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors E n)⟩

/-- The target of `mapDerivedCategoryHomologyIso` lifts homology followed by
the exact functor. -/
instance homologyFunctorCompLifting :
    Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ⋙ P)
      (DerivedCategory.homologyFunctor D n ⋙ P) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors D n) P⟩

/-- Cohomology of the functor induced by an exact functor on derived
categories is the image of cohomology under the exact functor. -/
def mapDerivedCategoryHomologyIso :
    P.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor E n ≅
      DerivedCategory.homologyFunctor D n ⋙ P :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.up ℤ) n)
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ⋙ P) _ _
    (mapHomologicalComplexHomologyIso P (ComplexShape.up ℤ) n)

/-- On a localized complex, `mapDerivedCategoryHomologyIso` is the homology
comparison of the termwise image. -/
lemma mapDerivedCategoryHomologyIso_hom_app_Q_obj (K : CochainComplex D ℤ) :
    (mapDerivedCategoryHomologyIso P n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor E n).map (P.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors E n).hom.app
          ((P.mapHomologicalComplex _).obj K) ≫
        ((K.sc n).mapHomologyIso P).hom ≫
        P.map ((DerivedCategory.homologyFunctorFactors D n).inv.app K) := by
  refine (Localization.liftNatTrans_app ..).trans ?_
  simp [Localization.Lifting.iso]
  rfl

/-- `mapDerivedCategoryHomologyIso` is natural. -/
@[reassoc]
lemma mapDerivedCategoryHomologyIso_hom_naturality {K L : DerivedCategory D} (u : K ⟶ L) :
    (DerivedCategory.homologyFunctor E n).map (P.mapDerivedCategory.map u) ≫
        (mapDerivedCategoryHomologyIso P n).hom.app L =
      (mapDerivedCategoryHomologyIso P n).hom.app K ≫
        P.map ((DerivedCategory.homologyFunctor D n).map u) :=
  (mapDerivedCategoryHomologyIso P n).hom.naturality u

end Homology

section Extend

variable {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  (P : D ⥤ E) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homology comparison of an exact functor is induced by its cycles
comparison. -/
@[reassoc]
lemma homologyπ_mapHomologyIso_hom (S : ShortComplex D) :
    (S.map P).homologyπ ≫ (S.mapHomologyIso P).hom =
      (S.mapCyclesIso P).hom ≫ P.map S.homologyπ := by
  have h₁ := congrArg Iso.hom (S.leftHomologyData.mapHomologyIso_eq P)
  have h₂ := congrArg Iso.hom (S.leftHomologyData.mapCyclesIso_eq P)
  rw [h₁, h₂]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    ShortComplex.LeftHomologyData.map_π, ← P.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  (K : HomologicalComplex D c) {j : ι} {j' : ι'} (hj : e.f j = j')

omit [PreservesFiniteLimits P] [PreservesFiniteColimits P] in
/-- The termwise comparison `mapExtendIso` in a degree coming from the original
complex is the image of the identification of the extended term. -/
lemma map_extendXIso_hom :
    P.map (K.extendXIso e hj).hom =
      (mapExtendIso P K e).inv.f j' ≫
        (((P.mapHomologicalComplex c).obj K).extendXIso e hj).hom := by
  have key : ∀ (o : Option ι) (h : o = some j),
      P.map (HomologicalComplex.extend.XIso K h).hom =
        (extendXMapIso P K o).inv ≫ (HomologicalComplex.extend.XIso _ h).hom := by
    rintro o rfl
    simp only [HomologicalComplex.extend.XIso, extendXMapIso, eqToIso.hom, eqToHom_map,
      Iso.refl_inv]
    exact (Category.id_comp _).symm
  exact key (e.r j') (e.r_eq_some hj)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cycles comparison of an exact functor is compatible with extension. -/
lemma mapCyclesIso_hom_map_extendCyclesIso_hom :
    (((K.extend e).sc j').mapCyclesIso P).hom ≫ P.map (K.extendCyclesIso e hj).hom =
      HomologicalComplex.cyclesMap (mapExtendIso P K e).inv j' ≫
        (((P.mapHomologicalComplex c).obj K).extendCyclesIso e hj).hom ≫
        ((K.sc j).mapCyclesIso P).hom := by
  refine (cancel_mono (P.map (K.iCycles j))).1 ?_
  have h₁ : (((K.extend e).sc j').mapCyclesIso P).hom ≫ P.map ((K.extend e).iCycles j') =
      ((P.mapHomologicalComplex c').obj (K.extend e)).iCycles j' :=
    ShortComplex.mapCyclesIso_hom_iCycles _ _
  have h₂ : ((K.sc j).mapCyclesIso P).hom ≫ P.map (K.iCycles j) =
      ((P.mapHomologicalComplex c).obj K).iCycles j :=
    ShortComplex.mapCyclesIso_hom_iCycles _ _
  simp only [Category.assoc, ← P.map_comp, HomologicalComplex.extendCyclesIso_hom_iCycles, h₂,
    HomologicalComplex.cyclesMap_i_assoc]
  rw [P.map_comp, reassoc_of% h₁, map_extendXIso_hom P e K hj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homology comparison of an exact functor is compatible with extension. -/
@[reassoc]
lemma mapHomologyIso_hom_map_extendHomologyIso_hom :
    (((K.extend e).sc j').mapHomologyIso P).hom ≫ P.map (K.extendHomologyIso e hj).hom =
      HomologicalComplex.homologyMap (mapExtendIso P K e).inv j' ≫
        (((P.mapHomologicalComplex c).obj K).extendHomologyIso e hj).hom ≫
        ((K.sc j).mapHomologyIso P).hom := by
  have h₁ : ((P.mapHomologicalComplex c').obj (K.extend e)).homologyπ j' ≫
      (((K.extend e).sc j').mapHomologyIso P).hom =
        (((K.extend e).sc j').mapCyclesIso P).hom ≫ P.map ((K.extend e).homologyπ j') :=
    homologyπ_mapHomologyIso_hom P ((K.extend e).sc j')
  have h₂ : ((P.mapHomologicalComplex c).obj K).homologyπ j ≫
      ((K.sc j).mapHomologyIso P).hom =
        ((K.sc j).mapCyclesIso P).hom ≫ P.map (K.homologyπ j) :=
    homologyπ_mapHomologyIso_hom P (K.sc j)
  refine (cancel_epi (((P.mapHomologicalComplex c').obj (K.extend e)).homologyπ j')).1 ?_
  rw [reassoc_of% h₁, ← P.map_comp, HomologicalComplex.homologyπ_extendHomologyIso_hom,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom_assoc, h₂, P.map_comp,
    ← Category.assoc, mapCyclesIso_hom_map_extendCyclesIso_hom P e K hj]
  simp only [Category.assoc]

end Extend

section ExtendComp

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  (F : C ⥤ D) [F.Additive] (P : D ⥤ E) [P.Additive]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')

/-- The inverse termwise comparison for a composite functor is the composite of
the inverse termwise comparisons. -/
lemma mapExtendIso_comp_inv (K : HomologicalComplex C c) :
    (mapExtendIso (F ⋙ P) K e).inv =
      (P.mapHomologicalComplex c').map (mapExtendIso F K e).inv ≫
        (mapExtendIso P ((F.mapHomologicalComplex c).obj K) e).inv := by
  have key : ∀ o : Option ι, (extendXMapIso (F ⋙ P) K o).inv =
      P.map (extendXMapIso F K o).inv ≫
        (extendXMapIso P ((F.mapHomologicalComplex c).obj K) o).inv
    | none => (HomologicalComplex.extend.isZero_X _ rfl).eq_of_tgt _ _
    | some _ => by
        simp only [extendXMapIso, Iso.refl_inv]
        exact ((Category.comp_id _).trans (P.map_id _)).symm
  ext i'
  exact key (e.r i')

end ExtendComp

section CompHomology

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  (G : C ⥤ D) [G.Additive] (P : D ⥤ E) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {H : C ⥤ E} [H.Additive] (e : G ⋙ P ≅ H)

omit [HasDerivedCategory C] [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
/-- On the localized image of a natural-indexed complex, exact postcomposition
followed by the termwise isomorphism induced by `e` is the localization
comparison of `P` followed by the termwise composite isomorphism. -/
lemma resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app
    (K : CochainComplex C ℕ) :
    (resolutionPostcompNatIso G P).hom.app K ≫ (resolutionCongrNatIso e).hom.app K =
      P.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat)) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app
            (K.extend ComplexShape.embeddingUpNat)) := by
  simp only [resolutionPostcompNatIso, resolutionCongrNatIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, Category.assoc]
  rw [← DerivedCategory.Q.map_comp]
  refine (Category.id_comp _).trans ?_
  refine congrArg (fun f => _ ≫ (DerivedCategory.Q (C := E)).map f) ?_
  ext i
  simp
  rfl

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P] in
/-- The termwise composite isomorphism commutes with undoing extension, for
the composite and for its two factors. -/
lemma mapHomologicalComplexCompIso_hom_app_extend_comp (K : CochainComplex C ℕ) :
    (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app
        (K.extend ComplexShape.embeddingUpNat) ≫
        (mapExtendIso H K ComplexShape.embeddingUpNat).inv =
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (mapExtendIso G K ComplexShape.embeddingUpNat).inv ≫
        (mapExtendIso P ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
          ComplexShape.embeddingUpNat).inv ≫
        HomologicalComplex.extendMap
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K)
          ComplexShape.embeddingUpNat := by
  have h := extendMapIso_hom_app ComplexShape.embeddingUpNat e.hom K
  simp only [extendMapIso, Iso.symm_hom] at h
  rw [mapExtendIso_comp_inv, Category.assoc] at h
  exact h

omit [HasDerivedCategory C] [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
/-- Cohomology of the resolution-model comparison for an exact composite: the
cohomology comparison of `P`, followed by the termwise composite isomorphism. -/
lemma resolutionPostcompCongr_homology (K : CochainComplex C ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor E (n : ℤ)).map
        ((resolutionPostcompNatIso G P).hom.app K ≫ (resolutionCongrNatIso e).hom.app K) ≫
        (derivedResolutionHomologyIso H K n).hom =
      (mapDerivedCategoryHomologyIso P (n : ℤ)).hom.app ((derivedResolutionFunctor G).obj K) ≫
        P.map (derivedResolutionHomologyIso G K n).hom ≫
        ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n).mapHomologyIso P).inv ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K) n := by
  have hQ : (mapDerivedCategoryHomologyIso P (n : ℤ)).hom.app
      ((derivedResolutionFunctor G).obj K) =
        (DerivedCategory.homologyFunctor E (n : ℤ)).map (P.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat))) ≫
        (DerivedCategory.homologyFunctorFactors E (n : ℤ)).hom.app
          ((P.mapHomologicalComplex _).obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat))) ≫
        ((((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat)).sc n).mapHomologyIso P).hom ≫
        P.map ((DerivedCategory.homologyFunctorFactors D (n : ℤ)).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat))) :=
    mapDerivedCategoryHomologyIso_hom_app_Q_obj P (n : ℤ) _
  have h₁ := (DerivedCategory.homologyFunctorFactors E (n : ℤ)).hom.naturality
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app
      (K.extend ComplexShape.embeddingUpNat))
  have h₂ := (mapHomologicalComplexHomologyIso P (ComplexShape.up ℤ) (n : ℤ)).hom.naturality
    (mapExtendIso G K ComplexShape.embeddingUpNat).inv
  have h₃ := mapHomologyIso_hom_map_extendHomologyIso_hom P ComplexShape.embeddingUpNat
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (j := n) (j' := (n : ℤ)) rfl
  have h₄ := HomologicalComplex.extendHomologyIso_hom_naturality
    (K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K)
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  have h₅ := congrArg (fun f => HomologicalComplex.homologyMap f (n : ℤ))
    (mapHomologicalComplexCompIso_hom_app_extend_comp G P e K)
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at h₁ h₂
  simp only [HomologicalComplex.homologyMap_comp] at h₅
  rw [resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app, Functor.map_comp,
    hQ]
  simp only [derivedResolutionHomologyIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, HomologicalComplex.homologyFunctor_map, Functor.map_comp, Category.assoc]
  rw [← P.map_comp_assoc, Iso.inv_hom_id_app]
  erw [P.map_id, Category.id_comp]
  congr 1
  erw [reassoc_of% h₁]
  congr 1
  erw [← reassoc_of% h₂, reassoc_of% h₃, Iso.hom_inv_id_assoc, ← h₄]
  erw [reassoc_of% h₅]

end CompHomology

section MapComp

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  (A : C ⥤ D) [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  (B : D ⥤ E) [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  (S : ShortComplex C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cycles comparison of a composite of exact functors is the composite of
the two cycles comparisons. -/
lemma mapCyclesIso_comp_hom :
    (S.mapCyclesIso (A ⋙ B)).hom =
      ((S.map A).mapCyclesIso B).hom ≫ B.map (S.mapCyclesIso A).hom := by
  have h₁ : (S.mapCyclesIso (A ⋙ B)).hom ≫ (A ⋙ B).map S.iCycles =
      (S.map (A ⋙ B)).iCycles :=
    ShortComplex.mapCyclesIso_hom_iCycles _ _
  have h₂ : ((S.map A).mapCyclesIso B).hom ≫ B.map (S.map A).iCycles =
      ((S.map A).map B).iCycles :=
    ShortComplex.mapCyclesIso_hom_iCycles _ _
  have h₃ : (S.mapCyclesIso A).hom ≫ A.map S.iCycles = (S.map A).iCycles :=
    ShortComplex.mapCyclesIso_hom_iCycles _ _
  have hm : Mono ((A ⋙ B).map S.iCycles) := by
    rw [(Iso.eq_inv_comp _).2 h₁]
    infer_instance
  refine (cancel_mono ((A ⋙ B).map S.iCycles)).1 ?_
  rw [h₁, Category.assoc, Functor.comp_map, ← B.map_comp, h₃, h₂]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homology comparison of a composite of exact functors is the composite
of the two homology comparisons. -/
lemma mapHomologyIso_comp_hom :
    (S.mapHomologyIso (A ⋙ B)).hom =
      ((S.map A).mapHomologyIso B).hom ≫ B.map (S.mapHomologyIso A).hom := by
  refine (cancel_epi (S.map (A ⋙ B)).homologyπ).1 ?_
  have h₁ := homologyπ_mapHomologyIso_hom (A ⋙ B) S
  have h₂ := homologyπ_mapHomologyIso_hom B (S.map A)
  have h₃ := homologyπ_mapHomologyIso_hom A S
  rw [h₁]
  erw [reassoc_of% h₂]
  rw [← B.map_comp, h₃, mapCyclesIso_comp_hom A B S, Category.assoc, B.map_comp]
  rfl

end MapComp

section RightDerivedComp

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  (G : C ⥤ D) [G.Additive] (P : D ⥤ E) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {H : C ⥤ E} [H.Additive] (e : G ⋙ P ≅ H)

/-- The classical comparison `P (Rⁿ G X) ≅ Rⁿ H X` for an exact functor `P` and
`e : G ⋙ P ≅ H`, computed with a specified injective resolution of `X`. -/
def rightDerivedCompIsoOfResolution {X : C} (I : InjectiveResolution X) (n : ℕ) :
    P.obj ((G.rightDerived n).obj X) ≅ (H.rightDerived n).obj X :=
  P.mapIso (I.isoRightDerivedObj G n) ≪≫
    ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso
      P).symm ≪≫
    (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).mapIso
      ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).app I.cocomplex) ≪≫
    (I.isoRightDerivedObj H n).symm

/-- The forward map of `rightDerivedCompIsoOfResolution`. -/
lemma rightDerivedCompIsoOfResolution_hom {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (rightDerivedCompIsoOfResolution G P e I n).hom =
      P.map (I.isoRightDerivedObj G n).hom ≫
        ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso
          P).inv ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app I.cocomplex) n ≫
        (I.isoRightDerivedObj H n).inv :=
  rfl

/-- The inverse map of `rightDerivedCompIsoOfResolution`. -/
lemma rightDerivedCompIsoOfResolution_inv {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (rightDerivedCompIsoOfResolution G P e I n).inv =
      (I.isoRightDerivedObj H n).hom ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).inv.app I.cocomplex) n ≫
        ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso
          P).hom ≫
        P.map (I.isoRightDerivedObj G n).inv :=
  (Category.assoc _ _ _).trans (Category.assoc _ _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- With the identity as the source functor, the comparison of
`DerivedComparison.compIsoOfResolution` is `rightDerivedCompIsoOfResolution`. -/
theorem compIsoOfResolution_id_hom {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (DerivedComparison.compIsoOfResolution G P (𝟭 C) H (e ≪≫ H.leftUnitor.symm) I n).hom =
      (rightDerivedCompIsoOfResolution G P e I n).hom := by
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 X)
    (DerivedComparison.mapInjectiveResolution (𝟭 C) I) I
    ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℕ)).hom.app I.cocomplex)
    (by
      rw [DerivedComparison.mapInjectiveResolution_ι_f_zero]
      simp [Functor.mapHomologicalComplexIdIso]) H n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  have hc : (DerivedComparison.complexIso G P (𝟭 C) H (e ≪≫ H.leftUnitor.symm)
      I.cocomplex).hom ≫ (H.mapHomologicalComplex _).map
        ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℕ)).hom.app I.cocomplex) =
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app I.cocomplex := by
    ext i
    simp [DerivedComparison.complexIso, Functor.mapHomologicalComplexIdIso]
  have hc' : (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
      (DerivedComparison.complexIso G P (𝟭 C) H (e ≪≫ H.leftUnitor.symm) I.cocomplex).hom ≫
      (H.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
        ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℕ)).hom.app I.cocomplex) =
      HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app I.cocomplex) n := by
    rw [Functor.comp_map, ← Functor.map_comp, hc]
    rfl
  rw [rightDerivedCompIsoOfResolution_hom]
  refine (congrArg (fun f => _ ≫ _ ≫ _ ≫ f) h).trans ?_
  exact congrArg (fun f => _ ≫ _ ≫ f) ((reassoc_of% hc') (I.isoRightDerivedObj H n).inv)

end RightDerivedComp

section CompHomologyIso

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  (G : C ⥤ D) [G.Additive] (P : D ⥤ E) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {H : C ⥤ E} [H.Additive] (e : G ⋙ P ≅ H)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Cohomology of `derivedCompIso` is the cohomology comparison of `P` followed
by the classical comparison `P (Rⁿ G X) ≅ Rⁿ H X`. -/
theorem derivedCompIso_hom_homology {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (DerivedCategory.homologyFunctor E (n : ℤ)).map ((derivedCompIso G P e).hom.app X) ≫
        (homologyIso H I n).hom =
      (mapDerivedCategoryHomologyIso P (n : ℤ)).hom.app
          ((derivedComplex G ⋙ DerivedCategory.Plus.ι).obj X) ≫
        P.map (homologyIso G I n).hom ≫ (rightDerivedCompIsoOfResolution G P e I n).hom := by
  rw [← derivedResolutionIso_homology H I n, ← derivedResolutionIso_homology G I n,
    ← Functor.map_comp_assoc, derivedCompIso_hom_resolution, Functor.map_comp,
    Category.assoc, reassoc_of% (resolutionPostcompCongr_homology G P e I.cocomplex n),
    mapDerivedCategoryHomologyIso_hom_naturality_assoc]
  simp only [rightDerivedCompIsoOfResolution, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, P.map_comp, Category.assoc]
  rw [← P.map_comp_assoc (I.isoRightDerivedObj G n).inv, Iso.inv_hom_id]
  erw [P.map_id, Category.id_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Inverse form of `derivedCompIso_hom_homology`. -/
theorem derivedCompIso_inv_homology {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (DerivedCategory.homologyFunctor E (n : ℤ)).map ((derivedCompIso G P e).inv.app X) ≫
        (mapDerivedCategoryHomologyIso P (n : ℤ)).hom.app
          ((derivedComplex G ⋙ DerivedCategory.Plus.ι).obj X) ≫
        P.map (homologyIso G I n).hom =
      (homologyIso H I n).hom ≫ (rightDerivedCompIsoOfResolution G P e I n).inv := by
  refine (Iso.eq_comp_inv _).2 ?_
  have h := derivedCompIso_hom_homology G P e I n
  simp only [Category.assoc]
  erw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

end CompHomologyIso

section RightDerivedCompCoherence

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {F : Type uF} [Category.{vF} F] [Abelian F]
  (Γ : C ⥤ D) [Γ.Additive]
  (A : D ⥤ E) [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  (B : E ⥤ F) [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  (Ac : D ⥤ F) [Ac.Additive] [PreservesFiniteLimits Ac] [PreservesFiniteColimits Ac]
  (c : Ac ≅ A ⋙ B)
  {G : C ⥤ E} [G.Additive] (eG : Γ ⋙ A ≅ G) {H : C ⥤ F} [H.Additive] (eH : Γ ⋙ Ac ≅ H)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The classical comparison for `G ⋙ B ≅ H` obtained from `Γ ⋙ A ≅ G`,
`Γ ⋙ Ac ≅ H` and `Ac ≅ A ⋙ B` is assembled from the comparisons for `A` and
`Ac`. -/
theorem rightDerivedCompIsoOfResolution_hom_comp {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (rightDerivedCompIsoOfResolution G B
        (Functor.isoWhiskerRight eG.symm B ≪≫ Functor.associator Γ A B ≪≫
          Functor.isoWhiskerLeft Γ c.symm ≪≫ eH) I n).hom =
      B.map (rightDerivedCompIsoOfResolution Γ A eG I n).inv ≫
        c.inv.app ((Γ.rightDerived n).obj X) ≫ (rightDerivedCompIsoOfResolution Γ Ac eH I n).hom := by
  let K := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have h₁ := c.inv.naturality_assoc (I.isoRightDerivedObj Γ n).inv
    (Ac.map (I.isoRightDerivedObj Γ n).hom)
  have h₂ := mapHomologyIso_comp_hom A B (K.sc n)
  have h₃ := NatTrans.app_homology c.inv (K.sc n)
  have h₄ : B.map (HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplexCompIso eG (ComplexShape.up ℕ)).inv.app I.cocomplex) n) ≫
      ((((A.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).sc n).mapHomologyIso B).inv =
      ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso B).inv ≫
        HomologicalComplex.homologyMap ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((Functor.mapHomologicalComplexCompIso eG (ComplexShape.up ℕ)).inv.app I.cocomplex)) n :=
    DerivedComparison.mapHomologyIso_inv_naturality B
      ((Functor.mapHomologicalComplexCompIso eG (ComplexShape.up ℕ)).inv.app I.cocomplex) n
  simp only [Functor.comp_map] at h₁
  rw [← Ac.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id] at h₁
  have hB : B.map ((K.sc n).mapHomologyIso A).hom =
      (((K.sc n).map A).mapHomologyIso B).inv ≫ ((K.sc n).mapHomologyIso (A ⋙ B)).hom :=
    (Iso.eq_inv_comp _).2 h₂.symm
  have key₀ : B.map ((K.sc n).mapHomologyIso A).hom ≫ c.inv.app (K.sc n).homology ≫
      ((K.sc n).mapHomologyIso Ac).inv =
        (((K.sc n).map A).mapHomologyIso B).inv ≫
          ShortComplex.homologyMap ((K.sc n).mapNatTrans c.inv) := by
    rw [hB, h₃]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have key : B.map ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso
        A).hom ≫
      c.inv.app ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) ≫
      ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso Ac).inv =
    ((((A.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).sc n).mapHomologyIso B).inv ≫
      ShortComplex.homologyMap
        ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapNatTrans c.inv) :=
    key₀
  have hfin : HomologicalComplex.homologyMap ((Functor.mapHomologicalComplexCompIso
        (Functor.isoWhiskerRight eG.symm B ≪≫ Functor.associator Γ A B ≪≫
          Functor.isoWhiskerLeft Γ c.symm ≪≫ eH) (ComplexShape.up ℕ)).hom.app I.cocomplex) n =
      HomologicalComplex.homologyMap ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((Functor.mapHomologicalComplexCompIso eG (ComplexShape.up ℕ)).inv.app I.cocomplex)) n ≫
        ShortComplex.homologyMap
          ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapNatTrans
            c.inv) ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso eH (ComplexShape.up ℕ)).hom.app I.cocomplex) n := by
    unfold HomologicalComplex.homologyMap
    erw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
    congr 1
    ext <;> simp [Functor.mapHomologicalComplexCompIso]
  rw [rightDerivedCompIsoOfResolution_hom, rightDerivedCompIsoOfResolution_inv,
    rightDerivedCompIsoOfResolution_hom]
  simp only [B.map_comp, Category.assoc]
  rw [reassoc_of% h₁]
  erw [reassoc_of% key]
  erw [reassoc_of% h₄]
  rw [reassoc_of% hfin]

end RightDerivedCompCoherence

end Langlands.Cohomology.DerivedPlus
