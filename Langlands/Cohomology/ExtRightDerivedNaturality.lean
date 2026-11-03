import Langlands.Cohomology.ExtRightDerived

/-! # Naturality in the second argument of the actual Ext/derived comparison -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.ExtRightDerived

open CategoryTheory CategoryTheory.Limits Opposite Abelian
open CochainComplex HomComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cocycle associated to a cycle of termwise Hom has the same components. -/
lemma coyonedaHomComplex_cycles_coe (X : C) (K : CochainComplex C ℤ) (n : ℤ)
    (c : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).cycles n) :
    ((HomComplex.leftHomologyData ((singleFunctor C 0).obj X) K n).cyclesIso.hom
      (HomologicalComplex.cyclesMap (coyonedaHomComplexIso X K).hom n c)).1 =
        Cochain.fromSingleMk
          ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).iCycles n c) (zero_add n) :=
  (ConcreteCategory.congr_hom
    (HomComplex.leftHomologyData ((singleFunctor C 0).obj X) K n).cyclesIso_hom_comp_i _).trans
      (ConcreteCategory.congr_hom
        (HomologicalComplex.cyclesMap_i (coyonedaHomComplexIso X K).hom n) c)

/-- The existing Hom/cohomology-class comparison on a cycle class. -/
lemma coyonedaHomologyAddEquiv_homologyπ (X : C) (K : CochainComplex C ℤ) (n : ℤ)
    (c : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).cycles n) :
    coyonedaHomologyAddEquiv X K n
        ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).homologyπ n c) =
      CohomologyClass.mk
        ((HomComplex.leftHomologyData ((singleFunctor C 0).obj X) K n).cyclesIso.hom
          (HomologicalComplex.cyclesMap (coyonedaHomComplexIso X K).hom n c)) := by
  change HomComplex.homologyAddEquiv _ _ n
    (((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homologyπ n ≫
      HomologicalComplex.homologyMap (coyonedaHomComplexIso X K).hom n) c) = _
  erw [HomologicalComplex.homologyπ_naturality]
  exact ConcreteCategory.congr_hom
    (HomComplex.leftHomologyData ((singleFunctor C 0).obj X) K n).homologyπ_comp_homologyIso_hom _

variable [HasExt.{w} C]

/-- The Ext/Hom-resolution comparison sends the class of a cycle to the existing
injective-resolution `extMk` constructor with that cycle as coefficient. -/
lemma extAddEquivHomology_symm_homologyπ (X : C) {Y : C} (R : InjectiveResolution Y)
    (n : ℕ)
    (c : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj R.cocomplex).cycles n) :
    (extAddEquivHomology X R n).symm
        ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj R.cocomplex).homologyπ n c) =
      R.extMk
        ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj R.cocomplex).iCycles n c)
        (n + 1) rfl
        (ConcreteCategory.congr_hom
          (HomologicalComplex.iCycles_d
            (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj R.cocomplex) n (n + 1)) c) := by
  let P := preadditiveCoyoneda.obj (op X)
  let K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let e := DerivedPlus.mapExtendIso P R.cocomplex ComplexShape.embeddingUpNat
  let c' := HomologicalComplex.cyclesMap e.hom (n : ℤ)
    ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl).inv c)
  have hc' :
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex).iCycles n c' =
        K.iCycles n c ≫ (R.cochainComplexXIso n n rfl).inv := by
    change (HomologicalComplex.cyclesMap e.hom (n : ℤ) ≫
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        R.cochainComplex).iCycles n)
          ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n)
            (j' := (n : ℤ)) rfl).inv c) = _
    erw [HomologicalComplex.cyclesMap_i]
    change e.hom.f n
      (((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n)
        (j' := (n : ℤ)) rfl).inv ≫
          (K.extend ComplexShape.embeddingUpNat).iCycles n) c) = _
    erw [K.extendCyclesIso_inv_iCycles ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl]
    have h (i : Option ℕ) (hi : i = some n) :
        (HomologicalComplex.extend.XIso K hi).inv ≫
            (DerivedPlus.extendXMapIso P R.cocomplex i).hom =
          P.map (HomologicalComplex.extend.XIso R.cocomplex hi).inv := by
      subst i
      dsimp [HomologicalComplex.extend.XIso, DerivedPlus.extendXMapIso]
      exact (Category.id_comp _).trans (P.map_id _).symm
    change ((K.extendXIso ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ)) rfl).inv ≫ e.hom.f n) (K.iCycles n c) = _
    erw [h _ (ComplexShape.embeddingUpNat.r_eq_some rfl)]
    rfl
  have h₁ :
      (coyonedaHomologyAddEquiv X R.cochainComplex n).symm
          (R.extAddEquivCohomologyClass
            (R.extMk (K.iCycles n c) (n + 1) rfl
              (ConcreteCategory.congr_hom (K.iCycles_d n (n + 1)) c))) =
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          R.cochainComplex).homologyπ n c' := by
    apply (coyonedaHomologyAddEquiv X R.cochainComplex n).injective
    rw [AddEquiv.apply_symm_apply, coyonedaHomologyAddEquiv_homologyπ,
      InjectiveResolution.extAddEquivCohomologyClass_apply,
      InjectiveResolution.extEquivCohomologyClass_extMk]
    congr 1
    ext : 1
    rw [coyonedaHomComplex_cycles_coe, hc']
    rfl
  have h₂ :
      (resolutionHomologyIso X R n).hom
          (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            R.cochainComplex).homologyπ n c') = K.homologyπ n c := by
    change ((K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom)
      (((((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          R.cochainComplex).homologyπ n) ≫
        HomologicalComplex.homologyMap e.inv (n : ℤ)) c') = _
    erw [HomologicalComplex.homologyπ_naturality]
    change (HomologicalComplex.cyclesMap e.inv (n : ℤ) ≫
      (K.extend ComplexShape.embeddingUpNat).homologyπ n ≫
      (K.extendHomologyIso ComplexShape.embeddingUpNat
        (j := n) (j' := (n : ℤ)) rfl).hom) c' = _
    erw [K.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl]
    dsimp [c']
    change K.homologyπ n
      (((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl).inv ≫
        HomologicalComplex.cyclesMap e.hom (n : ℤ) ≫
        HomologicalComplex.cyclesMap e.inv (n : ℤ) ≫
        (K.extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl).hom) c) = _
    erw [← HomologicalComplex.cyclesMap_comp_assoc, e.hom_inv_id,
      HomologicalComplex.cyclesMap_id, Category.id_comp, Iso.inv_hom_id]
    rfl
  apply (extAddEquivHomology X R n).injective
  rw [AddEquiv.apply_symm_apply]
  change _ = (resolutionHomologyIso X R n).hom
    ((coyonedaHomologyAddEquiv X R.cochainComplex n).symm
      (R.extAddEquivCohomologyClass _))
  rw [h₁, h₂]

/-- The inverse comparison is natural for a morphism of injective resolutions. -/
lemma extAddEquivHomology_symm_naturality (X : C) {Y Z : C} (f : Y ⟶ Z)
    (R : InjectiveResolution Y) (S : InjectiveResolution Z)
    (φ : InjectiveResolution.Hom R S f) (n : ℕ)
    (a : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj R.cocomplex).homology n) :
    (extAddEquivHomology X S n).symm
        (HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ.hom) n a) =
      ((extAddEquivHomology X R n).symm a).comp (Ext.mk₀ f) (add_zero n) := by
  let P := preadditiveCoyoneda.obj (op X)
  let K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let L := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj S.cocomplex
  let ψ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).1
    inferInstance a
  change (extAddEquivHomology X S n).symm
    ((K.homologyπ n ≫ HomologicalComplex.homologyMap ψ n) c) = _
  erw [HomologicalComplex.homologyπ_naturality]
  change (extAddEquivHomology X S n).symm
    (L.homologyπ n (HomologicalComplex.cyclesMap ψ n c)) = _
  rw [extAddEquivHomology_symm_homologyπ,
    extAddEquivHomology_symm_homologyπ, InjectiveResolution.extMk_comp_mk₀]
  congr 1
  exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ n) c

/-- The existing Ext/Hom-resolution comparison is natural in the coefficient. -/
lemma extAddEquivHomology_naturality (X : C) {Y Z : C} (f : Y ⟶ Z)
    (R : InjectiveResolution Y) (S : InjectiveResolution Z)
    (φ : InjectiveResolution.Hom R S f) (n : ℕ) (a : Ext.{w} X Y n) :
    extAddEquivHomology X S n (a.comp (Ext.mk₀ f) (add_zero n)) =
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ.hom) n (extAddEquivHomology X R n a) := by
  apply (extAddEquivHomology X S n).symm.injective
  rw [AddEquiv.symm_apply_apply, extAddEquivHomology_symm_naturality,
    AddEquiv.symm_apply_apply]

variable [HasInjectiveResolutions C]

/-- The published actual Ext/right-derived comparison is natural in its second
argument, for every nonnegative degree. -/
lemma extAddEquivRightDerived_naturality (X : C) {Y Z : C} (f : Y ⟶ Z)
    (n : ℕ) (a : Ext.{w} X Y n) :
    extAddEquivRightDerived X Z n (a.comp (Ext.mk₀ f) (add_zero n)) =
      ((preadditiveCoyoneda.obj (op X)).rightDerived n).map f
        (extAddEquivRightDerived X Y n a) := by
  let R := injectiveResolution Y
  let S := injectiveResolution Z
  let φ : InjectiveResolution.Hom R S f :=
    ⟨InjectiveResolution.desc f S R, by
      simp [InjectiveResolution.desc_commutes_zero]⟩
  change (S.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) n).inv
    (extAddEquivHomology X S n (a.comp (Ext.mk₀ f) (add_zero n))) =
      ((preadditiveCoyoneda.obj (op X)).rightDerived n).map f
        ((R.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) n).inv
          (extAddEquivHomology X R n a))
  rw [extAddEquivHomology_naturality X f R S φ]
  exact (ConcreteCategory.congr_hom
    (InjectiveResolution.isoRightDerivedObj_inv_naturality f R S φ.hom
      (by simp)
      (preadditiveCoyoneda.obj (op X)) n) (extAddEquivHomology X R n a)).symm

/-- Naturality of the inverse of the existing Ext/right-derived comparison. -/
lemma extAddEquivRightDerived_symm_naturality (X : C) {Y Z : C} (f : Y ⟶ Z)
    (n : ℕ) (a : ((preadditiveCoyoneda.obj (op X)).rightDerived n).obj Y) :
    (extAddEquivRightDerived X Z n).symm
        (((preadditiveCoyoneda.obj (op X)).rightDerived n).map f a) =
      ((extAddEquivRightDerived X Y n).symm a).comp (Ext.mk₀ f) (add_zero n) := by
  apply (extAddEquivRightDerived X Z n).injective
  rw [AddEquiv.apply_symm_apply, extAddEquivRightDerived_naturality,
    AddEquiv.apply_symm_apply]

omit [HasExt.{w} C] in
/-- When Ext is taken in the morphism universe, the unchanged comparison
components form a natural isomorphism to the right-derived Hom functor. -/
def extRightDerivedNatIso [HasExt.{v} C] (X : C) (n : ℕ) :
    extFunctorObj X n ≅ (preadditiveCoyoneda.obj (op X)).rightDerived n :=
  NatIso.ofComponents (fun Y => (extAddEquivRightDerived X Y n).toAddCommGrpIso)
    (fun {Y Z} f => by
      ext a
      exact extAddEquivRightDerived_naturality X f n a)

omit [HasExt.{w} C] in
/-- The natural isomorphism retains the published additive equivalences. -/
lemma extRightDerivedNatIso_app [HasExt.{v} C] (X Y : C) (n : ℕ) :
    (extRightDerivedNatIso X n).app Y =
      (extAddEquivRightDerived X Y n).toAddCommGrpIso := rfl

end Langlands.Cohomology.ExtRightDerived
