/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
-- Reuse the private generic postcomposition comparisons only in this proof.
import all WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-!
# Free sheaves and derived global sections

Source: Stacks Project, Derived Categories, Definition 015A and Lemma 05TI,
combined with the free-sheaf sections adjunction.
(blueprint: lem-weil-pbc-free-sheaf-derived-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open CochainComplex HomComplex

private noncomputable abbrev terminalFree (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :=
  (Etale.freeSheaf Λ X).obj (Scheme.Etale.mk (𝟙 X))

private noncomputable def terminalSections (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :=
  sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (CategoryTheory.evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))

private instance terminalSections_additive (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] : (terminalSections X Λ).Additive := by
  dsimp [terminalSections]
  infer_instance

private noncomputable def sectionsEquiv (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (terminalFree X Λ ⟶ F) ≃+ (terminalSections X Λ).obj F where
  toEquiv := Etale.freeSheafHomEquiv Λ (Scheme.Etale.mk (𝟙 X)) F
  map_add' a b := by
    change Etale.freeSheafHomEquiv Λ (Scheme.Etale.mk (𝟙 X)) F (a + b) =
      Etale.freeSheafHomEquiv Λ (Scheme.Etale.mk (𝟙 X)) F a +
        Etale.freeSheafHomEquiv Λ (Scheme.Etale.mk (𝟙 X)) F b
    simp only [Etale.freeSheafHomEquiv_apply]
    exact ((Etale.freeSheafSections Λ F).app (op (Scheme.Etale.mk (𝟙 X)))).hom.map_add a b

private lemma sectionsEquiv_naturality (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ G)
    (a : terminalFree X Λ ⟶ F) :
    sectionsEquiv X Λ G (a ≫ f) =
      (terminalSections X Λ).map f (sectionsEquiv X Λ F a) :=
  Etale.freeSheafHomEquiv_comp Λ (Scheme.Etale.mk (𝟙 X)) a f

end AlgebraicGeometry.Scheme

namespace FreeSheafComparisonAux

open CochainComplex HomComplex Limits Opposite

variable {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
  [HasDerivedCategory.{u + 1} C] [HasExt.{u + 1} C] [EnoughInjectives C]
  {Λ : Type (u + 1)} [CommRing Λ]
  (E : C ⥤ ModuleCat.{u + 1} Λ) [E.Additive] (A : C)
  (e : ∀ B : C, (A ⟶ B) ≃+
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj (E.obj B))
  (hnat : ∀ {B B' : C} (f : B ⟶ B') (a : A ⟶ B),
    e B' (a ≫ f) = (E.map f) (e B a))

include E A e hnat

set_option backward.isDefEq.respectTransparency false in
private noncomputable def complexSectionsIso (K : CochainComplex (C) ℤ) :
    HomComplex ((CochainComplex.singleFunctor _ 0).obj (A)) K ≅
      ((E ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((Cochain.fromSingleEquiv (zero_add n)).trans
      (e (K.X n))).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
        simpa [HomComplex, Cochain.δ_fromSingleMk,
          Cochain.fromSingleEquiv_fromSingleMk] using!
          (hnat (K.d i j) a).symm)

omit [HasDerivedCategory C] [HasExt C] [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
private lemma complexSectionsIso_naturality {K L : CochainComplex (C) ℤ}
    (f : K ⟶ L) :
    EtaleComparisonAux.postMap ((CochainComplex.singleFunctor _ 0).obj (A)) f ≫
        (complexSectionsIso E A e hnat L).hom =
      (complexSectionsIso E A e hnat K).hom ≫
        ((E ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapHomologicalComplex
          _).map f := by
  ext n a
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a n (zero_add n)
  change e (L.X n)
    ((Cochain.fromSingleEquiv (zero_add n))
      ((Cochain.fromSingleMk a (zero_add n)).comp (.ofHom f) (add_zero n))) =
    (E ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map (f.f n)
      (e (K.X n)
        ((Cochain.fromSingleEquiv (zero_add n)) (Cochain.fromSingleMk a (zero_add n))))
  rw [← Cochain.fromSingleMk_postcomp]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  exact hnat (f.f n) a

private noncomputable def classSectionsIso (K : CochainComplex (C) ℤ) (n : ℤ) :
    AddCommGrpCat.of
        (CohomologyClass ((CochainComplex.singleFunctor _ 0).obj (A)) K n) ≅
      (((E ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapHomologicalComplex _).obj
        K).homology n :=
  (leftHomologyData _ K n).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (complexSectionsIso E A e hnat K)

omit [HasDerivedCategory C] [HasExt C] [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
private lemma classSectionsIso_naturality {K L : CochainComplex (C) ℤ}
    (f : K ⟶ L) (n : ℤ) :
    AddCommGrpCat.ofHom (EtaleComparisonAux.postClass f n) ≫
        (classSectionsIso E A e hnat L n).hom =
      (classSectionsIso E A e hnat K n).hom ≫ HomologicalComplex.homologyMap
        (((E ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapHomologicalComplex _).map
          f) n := by
  have h := EtaleComparisonAux.homologyClass_naturality
    (S := (CochainComplex.singleFunctor _ 0).obj (A)) f n
  have h' := congrArg ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).map)
    (complexSectionsIso_naturality E A e hnat f)
  simp only [HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyMap_comp] at h'
  dsimp only [classSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← cancel_epi (leftHomologyData _ K n).homologyIso.hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% h, Iso.hom_inv_id_assoc]
  exact h'

private noncomputable def extSectionsIso (F : C) (n : ℕ) :
    (Abelian.extFunctorObj.{u + 1} (A) n).obj F ≅
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (((E).rightDerived n).obj F) :=
  (injectiveResolution F).extAddEquivCohomologyClass.toAddCommGrpIso ≪≫
    classSectionsIso E A e hnat (injectiveResolution F).cochainComplex n ≪≫
    ((((E).mapHomologicalComplex (.up ℤ)).obj
      (injectiveResolution F).cochainComplex).sc (n : ℤ)).mapHomologyIso
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≪≫
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
      ((injectiveResolution F).isoRightDerivedObjCochainComplex
        (E) n).symm

omit [HasDerivedCategory C] in
set_option backward.isDefEq.respectTransparency false in
private lemma extSectionsIso_naturality {F G : C} (f : F ⟶ G) (n : ℕ) :
    (Abelian.extFunctorObj.{u + 1} (A) n).map f ≫
        (extSectionsIso E A e hnat G n).hom =
      (extSectionsIso E A e hnat F n).hom ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (((E).rightDerived n).map f) := by
  let φ : (injectiveResolution F).Hom (injectiveResolution G) f :=
    ⟨InjectiveResolution.desc f _ _, by simp [InjectiveResolution.desc_commutes_zero]⟩
  have he : (Abelian.extFunctorObj.{u + 1} (A) n).map f ≫
      (injectiveResolution G).extAddEquivCohomologyClass.toAddCommGrpIso.hom =
    (injectiveResolution F).extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
      AddCommGrpCat.ofHom (EtaleComparisonAux.postClass φ.hom' (n : ℤ)) := by
    ext a
    exact (EtaleComparisonAux.extClass_naturality f _ _ φ n a).symm
  have hc := classSectionsIso_naturality E A e hnat φ.hom' (n : ℤ)
  have hu := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ (n : ℤ)).map
      (((E).mapHomologicalComplex _).map φ.hom'))
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hr := congrArg
    (fun a ↦ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map a)
    ((injectiveResolution F).isoRightDerivedObjCochainComplex_inv_naturality
      φ (E) n)
  dsimp only [extSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [reassoc_of% he, reassoc_of% hc]
  erw [reassoc_of% hu]
  simp only [Functor.map_comp] at hr
  erw [← Category.assoc, hr]
  simp only [Category.assoc]

private noncomputable def plusHomEquiv (F : C) (n : ℕ) :
    (((DerivedCategory.Plus.singleFunctor C 0).obj A) ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj F)⟦(n : ℤ)⟧) ≃+
      Abelian.Ext.{u + 1} A F n :=
  (show (((DerivedCategory.Plus.singleFunctor C 0).obj A) ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj F)⟦(n : ℤ)⟧) ≃+
      (((DerivedCategory.singleFunctor C 0).obj A) ⟶
        ((DerivedCategory.singleFunctor C 0).obj F)⟦(n : ℤ)⟧) from
    { toFun := fun f ↦ DerivedCategory.Plus.ι.map f ≫
        (DerivedCategory.Plus.ι.commShiftIso (n : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj F)
      invFun := fun f ↦ DerivedCategory.Plus.ι.preimage
        (f ≫ (DerivedCategory.Plus.ι.commShiftIso (n : ℤ)).inv.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj F))
      left_inv := by
        intro f
        dsimp only
        rw [Category.assoc, Iso.hom_inv_id_app]
        erw [Category.comp_id]
        exact Functor.preimage_map f
      right_inv := by
        intro f
        dsimp only
        rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app]
        erw [Category.comp_id]
      map_add' := by
        intro f g
        rw [Functor.map_add, Preadditive.add_comp] }).trans Abelian.Ext.homAddEquiv.symm

omit E e hnat [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
private lemma plusHomEquiv_naturality {F G : C} (f : F ⟶ G)
    (n : ℕ) (a : ((DerivedCategory.Plus.singleFunctor C 0).obj A) ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj F)⟦(n : ℤ)⟧) :
    plusHomEquiv A G n (a ≫ ((DerivedCategory.Plus.singleFunctor C 0).map f)⟦(n : ℤ)⟧') =
      (plusHomEquiv A F n a).comp (Abelian.Ext.mk₀ f) (add_zero n) := by
  apply Abelian.Ext.homAddEquiv.injective
  change ((plusHomEquiv A G n) _).hom =
    ((plusHomEquiv A F n a).comp (Abelian.Ext.mk₀ f) (add_zero n)).hom
  rw [← Abelian.Ext.hom_comp_singleFunctor_map_shift]
  change Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm _) =
    Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm _) ≫ _
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  change DerivedCategory.Plus.ι.map (a ≫ _) ≫ _ =
    (DerivedCategory.Plus.ι.map a ≫ _) ≫ _
  rw [Functor.map_comp, Category.assoc]
  simpa only [Category.assoc, Functor.comp_map] using!
    congrArg (DerivedCategory.Plus.ι.map a ≫ ·)
    ((DerivedCategory.Plus.ι.commShiftIso (n : ℤ)).hom.naturality
      ((DerivedCategory.Plus.singleFunctor C 0).map f))

end FreeSheafComparisonAux

namespace AlgebraicGeometry.Scheme

/-- Shifted maps from the free module sheaf on the terminal etale object compute derived
module global sections, naturally in the coefficient sheaf. No compactness, separation,
or torsion hypothesis is needed.

Source: Stacks Project, Derived Categories, Definition 015A and Lemma 05TI; the
identification with derived functors in lem-sp-derived-functor-single-identification.
(blueprint: lem-weil-pbc-free-sheaf-derived-sections).

Proof: For each module sheaf F choose an injective resolution F -> I in degrees >= 0.
The resolution is K-injective. Thus maps from the degree-zero free sheaf to F[q] in
D+ are degree-q cohomology classes of the Hom complex from the degree-zero free sheaf
into I. In every degree, the free-sheaf sections equivalence identifies this Hom
complex with the underlying abelian complex of I evaluated at the terminal object.
The equivalence is additive and commutes with differentials, by naturality of
freeSheafHomEquiv_comp. Evaluation at a terminal object is naturally isomorphic to
module global sections, so the latter complex is the underlying abelian complex of
Gamma(I). The exact forgetful functor from modules to abelian groups preserves
homology. By K-injectivity Gamma(I) computes derived global sections of F[0].
Taking homology gives the required component isomorphism. For a morphism F -> G,
lift it to the injective resolutions; the free-sheaf sections equivalence commutes
with this lift term by term. The induced cohomology maps therefore agree. Lifts are
unique up to homotopy, making the comparison natural and independent of choices.
The bounded-below inclusion is fully faithful, so its Hom computation agrees with
that in the unbounded derived category used on the right. This includes q = 0,
the zero coefficient ring, and the empty scheme. -/
theorem nonempty_freeSheafDerivedSectionsIso (Z : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (q : ℕ) :
    Nonempty
      ((DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ (q : ℤ) ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((Etale.freeSheaf Λ Z).obj
              (MorphismProperty.Over.mk ⊤ (𝟙 Z) (inferInstance : Etale (𝟙 Z))))))) ≅
        (DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
          Etale.cohomology (ModuleCat.{u + 1} Λ) Z (q : ℤ) ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  let E := terminalSections Z Λ
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let Γ := Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let e : (DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ (q : ℤ) ⋙
      preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (terminalFree Z Λ)))) ≅
      Abelian.extFunctorObj.{u + 1} (terminalFree Z Λ) q :=
    NatIso.ofComponents (fun F ↦
      (FreeSheafComparisonAux.plusHomEquiv (terminalFree Z Λ) F q).toAddCommGrpIso) (by
        intro F G f
        ext a
        exact FreeSheafComparisonAux.plusHomEquiv_naturality (terminalFree Z Λ) f q a)
  let e' : Abelian.extFunctorObj.{u + 1} (terminalFree Z Λ) q ≅
      E.rightDerived q ⋙ U :=
    NatIso.ofComponents (fun F ↦
      FreeSheafComparisonAux.extSectionsIso E (terminalFree Z Λ) (sectionsEquiv Z Λ)
      (sectionsEquiv_naturality Z Λ) F q)
      (fun f ↦ FreeSheafComparisonAux.extSectionsIso_naturality E (terminalFree Z Λ)
        (sectionsEquiv Z Λ) (sectionsEquiv_naturality Z Λ) f q)
  let c : E ≅ Γ :=
    (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (MorphismProperty.Over.mkIdTerminal _ _)).symm
  let d : E.rightDerived q ≅ Γ.rightDerived q :=
    { hom := NatTrans.rightDerived c.hom q
      inv := NatTrans.rightDerived c.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, c.hom_inv_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, c.inv_hom_id,
        NatTrans.rightDerived_id] }
  let t : DerivedCategory.singleFunctor _ 0 ⋙
      Etale.cohomology (ModuleCat.{u + 1} Λ) Z (q : ℤ) ≅ Γ.rightDerived q :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
        Γ.rightDerivedFunctorPlusCompatibility.symm)
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (q : ℤ)) ≪≫
        Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q
  exact ⟨e ≪≫ e' ≪≫ Functor.isoWhiskerRight (d ≪≫ t.symm) U⟩

end AlgebraicGeometry.Scheme
