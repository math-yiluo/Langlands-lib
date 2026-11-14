import Langlands.AlgebraicGeometry.Modules.RelativeDerivedHomComparison
import Langlands.Cohomology.AcyclicResolution.DerivedComparisonComposite

/-! # The relative derived Hom comparison on a module in degree zero -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
open Langlands.Cohomology

namespace Langlands.Cohomology.EquivariantComposite

open CochainComplex HomComplex

universe w' w v₀ u₀

section ExtHom

variable {C : Type u₀} [Category.{v₀} C] [Abelian C] [HasDerivedCategory.{w} C]
  [HasExt.{w'} C]

/-- On a complex receiving a quasi-isomorphic augmentation from `Y`, the canonical
cycle-localization map sends a class to the derived morphism of the Ext class
obtained by mapping it into an injective resolution of `Y`. -/
lemma homologyDerivedMap_eq_ext_hom (A : C) {Y : C} (P : CochainComplex C ℤ)
    (ε : (CochainComplex.singleFunctor C 0).obj Y ⟶ P) [QuasiIso ε]
    (I : InjectiveResolution Y) (φ : P ⟶ I.cochainComplex) (hφ : ε ≫ φ = I.ι') (n : ℕ)
    (v : (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj P).homology n)
    (a : Abelian.Ext.{w'} A Y n)
    (ha : HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map φ) n v =
      (ExtRightDerived.coyonedaHomologyAddEquiv A I.cochainComplex n).symm
        (I.extAddEquivCohomologyClass a)) :
    homologyDerivedMap A P n v =
      a.hom ≫ ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app Y ≫
        DerivedCategory.Q.map ε)⟦(n : ℤ)⟧' := by
  have hε : IsIso (DerivedCategory.Q.map ε) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C) ε).2 inferInstance
  have hI : IsIso (DerivedCategory.Q.map I.ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C) I.ι').2 inferInstance
  have hφQ : DerivedCategory.Q.map φ =
      inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map I.ι' := by
    rw [← hφ, Functor.map_comp, IsIso.inv_hom_id_assoc]
  have : IsIso (DerivedCategory.Q.map φ) := by rw [hφQ]; infer_instance
  apply (cancel_mono ((DerivedCategory.Q.map φ)⟦(n : ℤ)⟧')).1
  rw [← homologyDerivedMap_naturality, ha]
  obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective (I.extAddEquivCohomologyClass a)
  have ha' : a = I.extEquivCohomologyClass.symm (CohomologyClass.mk z) := by
    rw [hz]
    exact (I.extEquivCohomologyClass.symm_apply_apply a).symm
  rw [← hz]
  change ((DerivedCategory.singleFunctorIsoCompQ C 0).app A).hom ≫
      classDerivedMap _ I.cochainComplex n
        (ExtRightDerived.coyonedaHomologyAddEquiv A I.cochainComplex n
          ((ExtRightDerived.coyonedaHomologyAddEquiv A I.cochainComplex n).symm
            (CohomologyClass.mk z))) = _
  rw [AddEquiv.apply_symm_apply, classDerivedMap_mk, ha',
    InjectiveResolution.extEquivCohomologyClass_symm_mk_hom]
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc, hφQ,
    IsIso.hom_inv_id_assoc, IsIso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end ExtHom

end Langlands.Cohomology.EquivariantComposite

namespace Langlands.Cohomology.DerivedSectionsHomComparison

open CochainComplex HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

/-- The exact image of an object placed in degree zero is its image placed in
degree zero. -/
def singleMapDerivedIso (X₀ : C) :
    U.mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X₀)) ≅
      (DerivedCategory.singleFunctor A 0).obj (U.obj X₀) :=
  U.mapDerivedCategory.mapIso ((DerivedCategory.Plus.singleFunctorιIso C 0).app X₀) ≪≫
    (U.mapDerivedCategorySingleFunctor 0).app X₀

/-- The image of the augmentation of an injective resolution, as a map of integer
complexes. -/
def resolutionImageAugmentation {X₀ : C} (R : InjectiveResolution X₀) :
    (CochainComplex.singleFunctor A 0).obj (U.obj X₀) ⟶
      (U.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex :=
  (U.mapCochainComplexSingleFunctor 0).inv.app X₀ ≫
    (U.mapHomologicalComplex (.up ℤ)).map R.ι'

omit [EnoughInjectives C] in
/-- The localized image augmentation is the degree-zero image of the resolution
isomorphism followed by the exact-functor comparison. -/
lemma singleMapDerivedIso_inv_comp {X₀ : C} (R : InjectiveResolution X₀) :
    (singleMapDerivedIso U X₀).inv ≫
        U.mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (DerivedPlus.singleIsoOfResolution R).hom) ≫
        U.mapDerivedCategory.map
          ((DerivedCategory.Plus.QCompιIso C).hom.app (DerivedPlus.resolutionPlus R)) ≫
        U.mapDerivedCategoryFactors.hom.app R.cochainComplex =
      (DerivedCategory.singleFunctorIsoCompQ A 0).hom.app (U.obj X₀) ≫
        DerivedCategory.Q.map (resolutionImageAugmentation U R) := by
  simp only [singleMapDerivedIso, DerivedPlus.singleIsoOfResolution, Iso.trans_inv,
    Functor.mapIso_inv, Iso.app_inv, Category.assoc, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_hom]
  rw [← U.mapDerivedCategory.map_comp_assoc, ← U.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc,
    DerivedCategory.singleFunctorIsoCompQ_hom_app, Category.id_comp]
  have h := U.mapDerivedCategoryFactors.hom.naturality R.ι'
  simp only [Functor.comp_map] at h
  erw [Category.comp_id]
  erw [h]
  have h2 := U.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X₀
  simp only [resolutionImageAugmentation, Functor.map_comp]
  rw [← h2, Category.assoc]

/-- On an object in degree zero, the derived sections/Hom comparison is computed
by the cycle-localization map on the image of any injective resolution. -/
lemma comparison_app_single {X₀ : C} (R : InjectiveResolution X₀) (n : ℤ)
    (w : G.obj ((DerivedCategory.Plus.homologyFunctor D n).obj
      (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (DerivedPlus.resolutionPlus R)))))
    (a : ShiftedHom ((DerivedCategory.singleFunctor A 0).obj Z)
      ((DerivedCategory.singleFunctor A 0).obj (U.obj X₀)) n)
    (ha : EquivariantComposite.homologyDerivedMap Z
        ((U.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex) n
        ((sectionsHomologyIso F G U Z e (DerivedPlus.resolutionPlus R) n).hom w) =
      a ≫ ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app (U.obj X₀) ≫
        DerivedCategory.Q.map (resolutionImageAugmentation U R))⟦n⟧') :
    (comparison F G U Z e n).app ((DerivedCategory.Plus.singleFunctor C 0).obj X₀)
        (ULift.up (G.map ((DerivedCategory.Plus.homologyFunctor D n).map
          (DerivedPlus.derivedComplexIso F R).inv) w)) =
      a ≫ (singleMapDerivedIso U X₀).inv⟦n⟧' := by
  let K := DerivedPlus.resolutionPlus R
  let s := DerivedPlus.singleIsoOfResolution R
  let y : (derivedSections F G n).obj ((DerivedCategory.Plus.singleFunctor C 0).obj X₀) :=
    ULift.up (G.map ((DerivedCategory.Plus.homologyFunctor D n).map
      (DerivedPlus.derivedComplexIso F R).inv) w)
  let κ : U.mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X₀)) ⟶
      DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex) :=
    U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map s.hom) ≫
      U.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C).hom.app K) ≫
      U.mapDerivedCategoryFactors.hom.app R.cochainComplex
  have : IsIso κ := by dsimp only [κ]; infer_instance
  change (comparison F G U Z e n).app _ y = _
  apply (cancel_mono (κ⟦n⟧')).1
  have hnat := ConcreteCategory.congr_hom ((comparison F G U Z e n).naturality s.hom) y
  have hunit := ConcreteCategory.congr_hom
    (unit_comparisonOnComplex_app F G U Z e K n) (ULift.up w)
  have h0 : (DerivedPlus.derivedComplexIso F R).inv ≫ F.rightDerivedFunctorPlus.map s.hom =
      F.rightDerivedFunctorPlusUnit.app K := by
    simp [DerivedPlus.derivedComplexIso, s, K]
  have hy : (derivedSections F G n).map s.hom y =
      (sectionsUnit F G n).app K (ULift.up w) := by
    apply ULift.ext
    have h1 : G.map ((DerivedCategory.Plus.homologyFunctor D n).map
          (DerivedPlus.derivedComplexIso F R).inv) ≫
        G.map ((DerivedCategory.Plus.homologyFunctor D n).map
          (F.rightDerivedFunctorPlus.map s.hom)) =
        G.map ((DerivedCategory.Plus.homologyFunctor D n).map
          (F.rightDerivedFunctorPlusUnit.app K)) := by
      rw [← G.map_comp, ← Functor.map_comp, h0]
    exact ConcreteCategory.congr_hom h1 w
  simp only [ConcreteCategory.comp_apply] at hnat hunit
  rw [hy] at hnat
  have hA3 := singleMapDerivedIso_inv_comp U R
  calc (comparison F G U Z e n).app _ y ≫ κ⟦n⟧' =
      (derivedHomFactors U Z n).hom.app K ((comparison F G U Z e n).app
        (DerivedCategory.Plus.Q.obj K) ((sectionsUnit F G n).app K (ULift.up w))) := by
        rw [hnat]
        change _ = ((comparison F G U Z e n).app _ y ≫
          (U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map s.hom))⟦n⟧') ≫
          (U.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C).hom.app K) ≫
            U.mapDerivedCategoryFactors.hom.app R.cochainComplex)⟦n⟧'
        simp only [κ, Functor.map_comp, Category.assoc]
    _ = (complexComparison F G U Z e n).app K (ULift.up w) := hunit
    _ = EquivariantComposite.homologyDerivedMap Z
        ((U.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex) n
        ((sectionsHomologyIso F G U Z e (DerivedPlus.resolutionPlus R) n).hom w) := rfl
    _ = a ≫ (singleMapDerivedIso U X₀).inv⟦n⟧' ≫ κ⟦n⟧' := by
        rw [ha, ← hA3, ← Functor.map_comp]
    _ = _ := by rw [Category.assoc]

omit [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory D]
  [G.PreservesHomology] [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
/-- The termwise transport of `sectionsComplexIso` to natural-indexed complexes. -/
lemma sectionsComplexIso_extend (K : CochainComplex C ℕ) {L : CochainComplex A ℕ}
    (ψ : (U.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    (DerivedPlus.mapExtendIso G ((F.mapHomologicalComplex (.up ℕ)).obj K)
        ComplexShape.embeddingUpNat).hom ≫
      (G.mapHomologicalComplex (.up ℤ)).map
        (DerivedPlus.mapExtendIso F K ComplexShape.embeddingUpNat).hom ≫
      (sectionsComplexIso F G U Z e (K.extend ComplexShape.embeddingUpNat)).hom ≫
      ((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).map
        ((DerivedPlus.mapExtendIso U K ComplexShape.embeddingUpNat).inv ≫
          HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat) ≫
      (DerivedPlus.mapExtendIso (preadditiveCoyoneda.obj (op Z)) L
        ComplexShape.embeddingUpNat).inv =
    HomologicalComplex.extendMap
      ((NatTrans.mapHomologicalComplex e.hom (.up ℕ)).app K ≫
        ((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℕ)).map ψ)
      ComplexShape.embeddingUpNat := by
  have c1 := DerivedPlus.mapExtendIso_comp_inv F G ComplexShape.embeddingUpNat K
  have c1' : (DerivedPlus.mapExtendIso G ((F.mapHomologicalComplex (.up ℕ)).obj K)
        ComplexShape.embeddingUpNat).hom ≫
      (G.mapHomologicalComplex (.up ℤ)).map
        (DerivedPlus.mapExtendIso F K ComplexShape.embeddingUpNat).hom =
      (DerivedPlus.mapExtendIso (F ⋙ G) K ComplexShape.embeddingUpNat).hom := by
    rw [← cancel_mono (DerivedPlus.mapExtendIso (F ⋙ G) K ComplexShape.embeddingUpNat).inv,
      Iso.hom_inv_id, c1]
    simp [← Functor.map_comp_assoc]
  have c2 := DerivedPlus.mapExtendIso_comp_inv U (preadditiveCoyoneda.obj (op Z))
    ComplexShape.embeddingUpNat K
  have c3 := AcyclicResolution.natTrans_app_extend_eq e.hom K
  have c4 := AcyclicResolution.map_extendMap_eq (preadditiveCoyoneda.obj (op Z)) ψ
  simp only [AcyclicResolution.extendHom] at c3 c4
  have c5 : (sectionsComplexIso F G U Z e (K.extend ComplexShape.embeddingUpNat)).hom =
      (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        (K.extend ComplexShape.embeddingUpNat) := by
    ext i : 1
    simp [sectionsComplexIso, Functor.mapHomologicalComplexCompIso]
  rw [reassoc_of% c1', c5, c3, Functor.map_comp, c4]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← reassoc_of% c2, Iso.hom_inv_id_assoc, HomologicalComplex.extendMap_comp]

omit [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory A]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
/-- The homology form of `sectionsComplexIso_extend`: on the image of an injective
resolution, `sectionsHomologyIso` followed by a transported lift agrees with the
natural-indexed termwise comparison. -/
lemma sectionsHomologyIso_extend [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X₀ : C} (R : InjectiveResolution X₀) (n : ℕ) {L : CochainComplex A ℕ} (ψ : (U.mapHomologicalComplex (.up ℕ)).obj R.cocomplex ⟶ L) :
    G.map (((F.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl).inv ≫
      G.map (HomologicalComplex.homologyMap
        (DerivedPlus.mapExtendIso F R.cocomplex ComplexShape.embeddingUpNat).hom n) ≫
      G.map (DerivedPlusSource.localizedHomologyIso
        (F.mapCochainComplexPlus.obj (DerivedPlus.resolutionPlus R)) n).inv ≫
      (sectionsHomologyIso F G U Z e (DerivedPlus.resolutionPlus R) n).hom ≫
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).map
          ((DerivedPlus.mapExtendIso U R.cocomplex ComplexShape.embeddingUpNat).inv ≫
            HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat)) n ≫
      HomologicalComplex.homologyMap
        (DerivedPlus.mapExtendIso (preadditiveCoyoneda.obj (op Z)) L
          ComplexShape.embeddingUpNat).inv n ≫
      ((((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℕ)).obj L).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl).hom =
    ((((F.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).sc n).mapHomologyIso G).inv ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex e.hom (.up ℕ)).app R.cocomplex ≫
          ((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℕ)).map ψ) n := by
  let K := (F.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  have s1 : G.map (DerivedPlusSource.localizedHomologyIso
        (F.mapCochainComplexPlus.obj (DerivedPlus.resolutionPlus R)) n).inv ≫
      (sectionsHomologyIso F G U Z e (DerivedPlus.resolutionPlus R) n).hom =
      ((((F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).sc n).mapHomologyIso G).inv ≫
        HomologicalComplex.homologyMap
          (sectionsComplexIso F G U Z e R.cochainComplex).hom n := by
    simp only [sectionsHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      HomologicalComplex.homologyMapIso_hom, ← G.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have s2 := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor D (.up ℤ) n).map
      (DerivedPlus.mapExtendIso F R.cocomplex ComplexShape.embeddingUpNat).hom) G
  change G.map (HomologicalComplex.homologyMap
      (DerivedPlus.mapExtendIso F R.cocomplex ComplexShape.embeddingUpNat).hom n) ≫
      ((((F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).sc n).mapHomologyIso G).inv =
    (((K.extend ComplexShape.embeddingUpNat).sc n).mapHomologyIso G).inv ≫
      HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℤ)).map
        (DerivedPlus.mapExtendIso F R.cocomplex ComplexShape.embeddingUpNat).hom) n at s2
  have s3 := DerivedPlus.mapHomologyIso_hom_map_extendHomologyIso_hom G
    ComplexShape.embeddingUpNat K (j := n) (j' := n) rfl
  have s3' : G.map (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv ≫
      (((K.extend ComplexShape.embeddingUpNat).sc n).mapHomologyIso G).inv =
      ((K.sc n).mapHomologyIso G).inv ≫
        (((G.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) rfl).inv ≫
        HomologicalComplex.homologyMap
          (DerivedPlus.mapExtendIso G K ComplexShape.embeddingUpNat).hom n := by
    rw [← cancel_epi (G.map (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom),
      ← cancel_epi (((K.extend ComplexShape.embeddingUpNat).sc n).mapHomologyIso G).hom]
    simp only [← G.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rw [reassoc_of% s3]
    simp only [Iso.hom_inv_id_assoc, ← HomologicalComplex.homologyMap_comp,
      Iso.inv_hom_id, HomologicalComplex.homologyMap_id]
    rfl
  have s4 := sectionsComplexIso_extend F G U Z e R.cocomplex ψ
  have s5 : HomologicalComplex.homologyMap
        (DerivedPlus.mapExtendIso G K ComplexShape.embeddingUpNat).hom n ≫
      HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℤ)).map
        (DerivedPlus.mapExtendIso F R.cocomplex ComplexShape.embeddingUpNat).hom) n ≫
      HomologicalComplex.homologyMap (sectionsComplexIso F G U Z e R.cochainComplex).hom n ≫
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).map
          ((DerivedPlus.mapExtendIso U R.cocomplex ComplexShape.embeddingUpNat).inv ≫
            HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat)) n ≫
      HomologicalComplex.homologyMap
        (DerivedPlus.mapExtendIso (preadditiveCoyoneda.obj (op Z)) L
          ComplexShape.embeddingUpNat).inv n =
      HomologicalComplex.homologyMap (HomologicalComplex.extendMap
        ((NatTrans.mapHomologicalComplex e.hom (.up ℕ)).app R.cocomplex ≫
          ((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℕ)).map ψ)
        ComplexShape.embeddingUpNat) n := by
    rw [← s4]
    simp only [HomologicalComplex.homologyMap_comp]
    rfl
  rw [reassoc_of% s1, reassoc_of% s2, reassoc_of% s3', reassoc_of% s5,
    HomologicalComplex.extendHomologyIso_hom_naturality]
  erw [Iso.inv_hom_id_assoc]

end Langlands.Cohomology.DerivedSectionsHomComparison

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

variable {R : CommRingCat.{u}} {X : Over (Spec R)}

/-- The exact image of a module placed in degree zero is the underlying abelian
sheaf placed in degree zero. -/
def singleToAbSheafIso (M : X.left.Modules) :
    (toAbSheaf X.left).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj
          ((DerivedCategory.Plus.singleFunctor X.left.Modules 0).obj M)) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((toAbSheaf X.left).obj M) :=
  (toAbSheaf X.left).mapDerivedCategory.mapIso
      ((DerivedCategory.Plus.singleFunctorιIso X.left.Modules 0).app M) ≪≫
    ((toAbSheaf X.left).mapDerivedCategorySingleFunctor 0).app M

/-- The comparison lift from the underlying abelian sheaves of the chosen injective
resolution of `M` to the chosen injective resolution of the underlying sheaf of `M`. -/
def resolutionLift (M : X.left.Modules) :
    ((toAbSheaf X.left).mapHomologicalComplex (.up ℕ)).obj (injectiveResolution M).cocomplex ⟶
      (injectiveResolution ((toAbSheaf X.left).obj M)).cocomplex :=
  haveI := AcyclicResolution.quasiIso_mapAugmentation (toAbSheaf X.left)
    (injectiveResolution M) (isZero_rightDerived_toAbSheaf X.left M)
  AcyclicResolution.lift
    (AcyclicResolution.mapAugmentation (toAbSheaf X.left) (injectiveResolution M))
    (𝟙 _) (injectiveResolution ((toAbSheaf X.left).obj M)).ι

lemma mapAugmentation_comp_resolutionLift (M : X.left.Modules) :
    AcyclicResolution.mapAugmentation (toAbSheaf X.left) (injectiveResolution M) ≫
        resolutionLift M = (injectiveResolution ((toAbSheaf X.left).obj M)).ι :=
  haveI := AcyclicResolution.quasiIso_mapAugmentation (toAbSheaf X.left)
    (injectiveResolution M) (isZero_rightDerived_toAbSheaf X.left M)
  AcyclicResolution.comp_lift_id _ _

/-- The integer-indexed comparison lift. -/
def resolutionLiftInt (M : X.left.Modules) :
    ((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj (injectiveResolution M).cochainComplex ⟶
      (injectiveResolution ((toAbSheaf X.left).obj M)).cochainComplex :=
  (DerivedPlus.mapExtendIso (toAbSheaf X.left) (injectiveResolution M).cocomplex
      ComplexShape.embeddingUpNat).inv ≫
    HomologicalComplex.extendMap (resolutionLift M) ComplexShape.embeddingUpNat

lemma resolutionImageAugmentation_comp_resolutionLiftInt (M : X.left.Modules) :
    DerivedSectionsHomComparison.resolutionImageAugmentation (toAbSheaf X.left)
        (injectiveResolution M) ≫ resolutionLiftInt M =
      (injectiveResolution ((toAbSheaf X.left).obj M)).ι' := by
  apply HomologicalComplex.from_single_hom_ext
  have h := congrArg (fun g => g.f 0) (mapAugmentation_comp_resolutionLift M)
  simp only [HomologicalComplex.comp_f, AcyclicResolution.mapAugmentation_f_zero] at h
  simp only [DerivedSectionsHomComparison.resolutionImageAugmentation, resolutionLiftInt,
    HomologicalComplex.comp_f, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, InjectiveResolution.ι'_f_zero, Category.assoc,
    Functor.map_comp]
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (by simp)]
  have h' : (toAbSheaf X.left).map ((injectiveResolution M).ι.f 0) ≫ (resolutionLift M).f 0 =
      (toAbSheaf X.left).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 M).hom ≫
        (injectiveResolution ((toAbSheaf X.left).obj M)).ι.f 0 := by
    rw [← h, Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Functor.map_comp_assoc (toAbSheaf X.left)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← reassoc_of% (DerivedPlus.map_extendXIso_hom (toAbSheaf X.left) ComplexShape.embeddingUpNat
    (injectiveResolution M).cocomplex (j := 0) (j' := 0) (by simp))]
  simp only [InjectiveResolution.cochainComplexXIso]
  rw [Iso.map_inv_hom_id_assoc, reassoc_of% h']
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]

/-- The actual relative comparison, written on the chosen injective resolutions. -/
lemma relativeCohomologyIso_hom_eq (M : X.left.Modules) (n : ℕ) :
    (relativeCohomologyIso X.hom M n).hom =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          ((injectiveResolution M).isoRightDerivedObj
            (DerivedSections.relativeGlobalSections X.hom) n).hom ≫
        (((((DerivedSections.relativeGlobalSections X.hom).mapHomologicalComplex (.up ℕ)).obj
          (injectiveResolution M).cocomplex).sc n).mapHomologyIso
            (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso (relativeGlobalSectionsForgetIso X.hom)
            (.up ℕ)).hom.app (injectiveResolution M).cocomplex) n ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso (globalSectionsIso X.left)
            (.up ℕ)).inv.app (injectiveResolution M).cocomplex) n ≫
        HomologicalComplex.homologyMap
          (((AbelianSheafDerivedSections.globalSections X.left.toTopCat).mapHomologicalComplex
            (.up ℕ)).map (resolutionLift M)) n ≫
        ((injectiveResolution ((toAbSheaf X.left).obj M)).isoRightDerivedObj
          (AbelianSheafDerivedSections.globalSections X.left.toTopCat) n).inv := by
  simp only [relativeCohomologyIso, forgetRelativeDerivedSectionsIso_app, Iso.trans_hom,
    asIso_hom, DerivedPlus.rightDerivedCompIsoOfResolution_hom,
    AcyclicResolution.compComparison, AcyclicResolution.resolutionComparison,
    AcyclicResolution.comparison, Category.assoc, Iso.inv_hom_id_assoc, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map]
  rfl

/-- The termwise maps in the actual relative comparison, followed by the inverse
Hom/sections identification on the target resolution, are the termwise sections/Hom
identification followed by the comparison lift. -/
lemma resolutionLift_sectionsHom (M : X.left.Modules) :
    (Functor.mapHomologicalComplexCompIso (relativeGlobalSectionsForgetIso X.hom)
        (.up ℕ)).hom.app (injectiveResolution M).cocomplex ≫
      (Functor.mapHomologicalComplexCompIso (globalSectionsIso X.left)
        (.up ℕ)).inv.app (injectiveResolution M).cocomplex ≫
      ((AbelianSheafDerivedSections.globalSections X.left.toTopCat).mapHomologicalComplex
        (.up ℕ)).map (resolutionLift M) ≫
      (NatTrans.mapHomologicalComplex
        (AbelianSheafDerivedSections.homGlobalSectionsIso X.left.toTopCat).inv (.up ℕ)).app
          (injectiveResolution ((toAbSheaf X.left).obj M)).cocomplex =
    (NatTrans.mapHomologicalComplex (relativeSectionsHomIso X.hom).hom (.up ℕ)).app
        (injectiveResolution M).cocomplex ≫
      ((preadditiveCoyoneda.obj (op (AbelianSheafDerivedSections.constantIntegers
        X.left.toTopCat))).mapHomologicalComplex (.up ℕ)).map (resolutionLift M) := by
  ext i : 1
  simp [relativeSectionsHomIso, relativeGlobalSectionsForgetIso, globalSectionsIso]

/-- Inverting the Hom/sections identification recovers the Ext-defined class on
any injective resolution. -/
lemma homologyMap_homGlobalSectionsIso_inv_apply {T : TopCat.{u}}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T} (I : InjectiveResolution B) (n : ℕ)
    (x : Sheaf.H.{u} B n) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
        (AbelianSheafDerivedSections.homGlobalSectionsIso T).inv (.up ℕ)).app I.cocomplex) n
        (AbelianSheafDerivedSections.resolutionGlobalSectionsHomologyEquiv T I n x) =
      ExtRightDerived.extAddEquivHomology (AbelianSheafDerivedSections.constantIntegers T)
        I n x :=
  (HomologicalComplex.homologyMapIso ((NatIso.mapHomologicalComplex
    (AbelianSheafDerivedSections.homGlobalSectionsIso T) (.up ℕ)).app I.cocomplex) n).hom_inv_id_apply
      _

/-- The Ext class of `x`, on the chosen injective resolution of the underlying
sheaf, is the image of the relative module class under the resolution lift. -/
lemma extAddEquivHomology_relativeHAddEquiv (M : X.left.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X.left).obj M) n) :
    ExtRightDerived.extAddEquivHomology
        (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
        (injectiveResolution ((toAbSheaf X.left).obj M)) n x =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (relativeSectionsHomIso X.hom).hom (.up ℕ)).app
            (injectiveResolution M).cocomplex ≫
          ((preadditiveCoyoneda.obj (op (AbelianSheafDerivedSections.constantIntegers
            X.left.toTopCat))).mapHomologicalComplex (.up ℕ)).map (resolutionLift M)) n
        ((((((DerivedSections.relativeGlobalSections X.hom).mapHomologicalComplex (.up ℕ)).obj
          (injectiveResolution M).cocomplex).sc n).mapHomologyIso
            (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv
          ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
            ((injectiveResolution M).isoRightDerivedObj
              (DerivedSections.relativeGlobalSections X.hom) n).hom
            (relativeHAddEquiv X.hom M n x))) := by
  have hMI : (relativeCohomologyIso X.hom M n).hom ≫
      ((injectiveResolution ((toAbSheaf X.left).obj M)).isoRightDerivedObj
        (AbelianSheafDerivedSections.globalSections X.left.toTopCat) n).hom ≫
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
        (AbelianSheafDerivedSections.homGlobalSectionsIso X.left.toTopCat).inv (.up ℕ)).app
          (injectiveResolution ((toAbSheaf X.left).obj M)).cocomplex) n =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          ((injectiveResolution M).isoRightDerivedObj
            (DerivedSections.relativeGlobalSections X.hom) n).hom ≫
        (((((DerivedSections.relativeGlobalSections X.hom).mapHomologicalComplex (.up ℕ)).obj
          (injectiveResolution M).cocomplex).sc n).mapHomologyIso
            (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (relativeSectionsHomIso X.hom).hom (.up ℕ)).app
              (injectiveResolution M).cocomplex ≫
            ((preadditiveCoyoneda.obj (op (AbelianSheafDerivedSections.constantIntegers
              X.left.toTopCat))).mapHomologicalComplex (.up ℕ)).map (resolutionLift M)) n := by
    rw [relativeCohomologyIso_hom_eq, ← resolutionLift_sectionsHom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, HomologicalComplex.homologyMap_comp]
  have h1 := relativeCohomologyIso_relativeHAddEquiv X.hom M n x
  rw [AbelianSheafDerivedSections.HAddEquiv_eq_of_resolution X.left.toTopCat
    (injectiveResolution ((toAbSheaf X.left).obj M)) n] at h1
  have h2 := ConcreteCategory.congr_hom hMI (relativeHAddEquiv X.hom M n x)
  simp only [ConcreteCategory.comp_apply] at h2
  rw [h1, Iso.inv_hom_id_apply] at h2
  exact (homologyMap_homGlobalSectionsIso_inv_apply _ n x).symm.trans h2

/-- On a module in degree zero, the relative derived sections/Hom comparison is
the inverse of the actual relative additive cohomology comparison, followed by
the derived-category morphism of the Ext class. -/
theorem relativeDerivedHomComparison_single (M : X.left.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X.left).obj M) n) :
    (relativeDerivedHomComparison X.hom (n : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor X.left.Modules 0).obj M)
        (ULift.up ((DerivedPlus.homologyIso (DerivedSections.relativeGlobalSections X.hom)
          (injectiveResolution M) n).inv (relativeHAddEquiv X.hom M n x))) =
      x.hom ≫ (CategoryTheory.shiftFunctor _ (n : ℤ)).map (singleToAbSheafIso M).inv := by
  let w := (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      ((((DerivedSections.relativeGlobalSections X.hom).mapHomologicalComplex (.up ℕ)).obj
          (injectiveResolution M).cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (j := n) rfl).inv
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((injectiveResolution M).isoRightDerivedObj
          (DerivedSections.relativeGlobalSections X.hom) n).hom
        (relativeHAddEquiv X.hom M n x))
  let w' := (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
    (DerivedPlusSource.localizedHomologyIso
      ((DerivedSections.relativeGlobalSections X.hom).mapCochainComplexPlus.obj
        (DerivedPlus.resolutionPlus (injectiveResolution M))) n).inv
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap (DerivedPlus.mapExtendIso
        (DerivedSections.relativeGlobalSections X.hom) (injectiveResolution M).cocomplex
          ComplexShape.embeddingUpNat).hom n) w)
  have : QuasiIso (DerivedSectionsHomComparison.resolutionImageAugmentation
      (toAbSheaf X.left) (injectiveResolution M)) := by
    dsimp only [DerivedSectionsHomComparison.resolutionImageAugmentation]
    infer_instance
  have hL : HomologicalComplex.homologyMap
      (((preadditiveCoyoneda.obj (op (AbelianSheafDerivedSections.constantIntegers
        X.left.toTopCat))).mapHomologicalComplex (.up ℤ)).map (resolutionLiftInt M)) n
        ((DerivedSectionsHomComparison.sectionsHomologyIso
          (DerivedSections.relativeGlobalSections X.hom)
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
          (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
          (relativeSectionsHomIso X.hom) (DerivedPlus.resolutionPlus (injectiveResolution M))
            n).hom w') =
      (ExtRightDerived.coyonedaHomologyAddEquiv
        (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
        (injectiveResolution ((toAbSheaf X.left).obj M)).cochainComplex n).symm
        ((injectiveResolution ((toAbSheaf X.left).obj M)).extAddEquivCohomologyClass x) := by
    apply (ExtRightDerived.resolutionHomologyIso
      (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
      (injectiveResolution ((toAbSheaf X.left).obj M)) n).addCommGroupIsoToAddEquiv.injective
    change _ = ExtRightDerived.extAddEquivHomology
      (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
      (injectiveResolution ((toAbSheaf X.left).obj M)) n x
    rw [extAddEquivHomology_relativeHAddEquiv]
    have key := ConcreteCategory.congr_hom
      (DerivedSectionsHomComparison.sectionsHomologyIso_extend
        (DerivedSections.relativeGlobalSections X.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
        (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
        (relativeSectionsHomIso X.hom) (injectiveResolution M) n (resolutionLift M))
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((injectiveResolution M).isoRightDerivedObj
          (DerivedSections.relativeGlobalSections X.hom) n).hom
        (relativeHAddEquiv X.hom M n x))
    simp only [ConcreteCategory.comp_apply] at key
    exact key
  have ha : EquivariantComposite.homologyDerivedMap
      (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
      (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
        (injectiveResolution M).cochainComplex) n
      ((DerivedSectionsHomComparison.sectionsHomologyIso
          (DerivedSections.relativeGlobalSections X.hom)
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
          (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
          (relativeSectionsHomIso X.hom) (DerivedPlus.resolutionPlus (injectiveResolution M))
            n).hom w') =
      x.hom ≫ ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app ((toAbSheaf X.left).obj M) ≫
        DerivedCategory.Q.map (DerivedSectionsHomComparison.resolutionImageAugmentation
          (toAbSheaf X.left) (injectiveResolution M)))⟦(n : ℤ)⟧' :=
    EquivariantComposite.homologyDerivedMap_eq_ext_hom
    (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
    (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj (injectiveResolution M).cochainComplex)
    (DerivedSectionsHomComparison.resolutionImageAugmentation (toAbSheaf X.left)
      (injectiveResolution M))
    (injectiveResolution ((toAbSheaf X.left).obj M)) (resolutionLiftInt M)
    (resolutionImageAugmentation_comp_resolutionLiftInt M) n _ x hL
  exact DerivedSectionsHomComparison.comparison_app_single
    (DerivedSections.relativeGlobalSections X.hom)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
    (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
    (relativeSectionsHomIso X.hom) (injectiveResolution M) (n : ℤ) w' x.hom ha

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
