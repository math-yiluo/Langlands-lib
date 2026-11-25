/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact

/-!
# Direct image and finite coefficient restriction in the fixed scalar presentation

The comparison is the actual adjunction mate of the canonical inverse-image comparison.

## References

* Stacks Tag 03D6
* Stacks Tag 07A6
* Stacks Tag 0D6E
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
-- Avoid an unrelated derived-adjoint search while elaborating the mate identities.
-- Restore the imported instance at the end of this module.
attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

private theorem mate_left_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L E : A ⥤ B} {R : B ⥤ A} {L' E' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : L ≅ E) (e' : L' ≅ E')
    (s : G ⋙ E' ⟶ E ⋙ H) :
    (mateEquiv (adj.ofNatIsoLeft e) (adj'.ofNatIsoLeft e')
      (TwoSquare.mk _ _ _ _ s)) =
      (mateEquiv adj adj'
        (TwoSquare.mk _ _ _ _
          (Functor.whiskerLeft G e'.hom ≫ s ≫ Functor.whiskerRight e.inv H))) := by
  ext X
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Functor.map_comp, Functor.comp_map, Category.assoc]
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  rfl

private theorem derived_mate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (m : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (t : R ⋙ G ⟶ H ⋙ R') [IsIso t]
    (hm : m = (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom)))
    (ht : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) = t)
    (hres : ∀ I : CochainComplex B ℤ, I.IsKInjective →
      ∀ J : CochainComplex D ℤ, J.IsKInjective →
      ∀ j : (H.mapHomologicalComplex (.up ℤ)).obj I ⟶ J,
        QuasiIso j → QuasiIso ((R'.mapHomologicalComplex (.up ℤ)).map j)) :
    IsIso m := by
  have : IsIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) := by
    rw [ht]
    infer_instance
  have hI (I : CochainComplex B ℤ) [I.IsKInjective] :
      IsIso (m.app (_root_.DerivedCategory.Q.obj I)) := by
    obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((H.mapHomologicalComplex (.up ℤ)).obj I)
    have : J.IsKInjective := hJ
    have : QuasiIso j := hj
    have : QuasiIso ((R'.mapHomologicalComplex (.up ℤ)).map j) :=
      hres I inferInstance J inferInstance j inferInstance
    have : IsIso (chainDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj I)) :=
      chainDerivedUnit_isIso_of_resolution R' _ J j
    have : IsIso (chainDerivedUnit R I) := chainDerivedUnit_isIso R I
    have : IsIso ((NatTrans.mapHomologicalComplex
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app I) := by
      change IsIso (((NatIso.mapHomologicalComplex
        (asIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)))
        (.up ℤ)).app I).hom)
      infer_instance
    have hi := derived_mate_factors adj adj' s I
    have hi' := (congrArg (fun z ↦ G.mapDerivedCategory.map (chainDerivedUnit R I) ≫
      z.app (_root_.DerivedCategory.Q.obj I) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) hm).trans hi
    have : IsIso (G.mapDerivedCategory.map (chainDerivedUnit R I) ≫
        m.app (_root_.DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) := by
      rw [hi']
      infer_instance
    have : IsIso (m.app (_root_.DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) :=
      IsIso.of_isIso_comp_left (G.mapDerivedCategory.map (chainDerivedUnit R I)) _
    exact IsIso.of_isIso_comp_right _
      (R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I))
  have (K : _root_.DerivedCategory B) : IsIso (m.app K) := by
    obtain ⟨I, hInj, ⟨eI⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_of_isKInjective K
    have : I.IsKInjective := hInj
    have : IsIso (m.app (_root_.DerivedCategory.Q.obj I)) := hI I
    have hn := m.naturality eI.hom
    have : IsIso (m.app K ≫ (H.mapDerivedCategory ⋙ R'.rightDerivedFunctor).map eI.hom) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((H.mapDerivedCategory ⋙ R'.rightDerivedFunctor).map eI.hom)
  exact NatIso.isIso_of_isIso_app m

namespace AlgebraicGeometry.ProEtale

private theorem restriction_underived_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom)) =
        𝟙 (lowerStar (ModuleCat.{u + 1} B) f ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ) := by
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) φ)).injective
  rw [iterated_mateEquiv_conjugateEquiv]
  rw [conjugateEquiv_upperStarRestrictScalarsIso_hom]
  ext M ⟨U⟩ x
  exact congrArg (fun t ↦ t.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
      (M.obj.obj (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U)))).symm

/-- The sectionwise coefficient square, cached with its two explicit composite functor types. -/
@[no_expose] noncomputable def fixedScalarRestrictionDirectImageUnderived
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    lowerStar (ModuleCat.{u + 1} B) f ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙ lowerStar (ModuleCat.{u + 1} A) f :=
  Iso.refl _

attribute [local irreducible] upperStar

/-- The canonical inverse-image/restriction square, with its normalization. -/
noncomputable abbrev fixedScalarRestrictionPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  leftDerivedUpperStarRestrictScalarsIso φ f

/-- The inverse-direction direct-image comparison is the mate of the canonical square. -/
@[no_expose] noncomputable def fixedScalarRestrictionDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ ⟶
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (fixedScalarRestrictionPullback φ f).hom
private noncomputable abbrev restrictionDerivedUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (_root_.DerivedCategory.Q.obj K) :=
  F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)

private theorem chainDerivedUnit_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    chainDerivedUnit F K = restrictionDerivedUnit F K := by
  dsimp only [chainDerivedUnit]
  rw [quotient_hom_id, quotient_inv_id]
  erw [F.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]

private theorem simple_derived_mate_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (K : CochainComplex B ℤ) :
    G.mapDerivedCategory.map (restrictionDerivedUnit R K) ≫
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategoryCompIso G L' ≪≫
            Functor.mapDerivedCategoryNatIso s ≪≫
            (Functor.mapDerivedCategoryCompIso L H).symm).hom)).app (DerivedCategory.Q.obj K) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app K) =
    G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app K) ≫
      restrictionDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj K) := by
  have h := derived_mate_factors adj adj' s K
  rw [chainDerivedUnit_eq, chainDerivedUnit_eq] at h
  exact h

private theorem comparison_normalization
    {C : Type*} [Category C] {X Y Z V W P T : C}
    (u : X ⟶ Y) (m : Y ⟶ Z) (a : Z ⟶ W) (b : X ⟶ V)
    (v : V ⟶ W) (q : V ⟶ P) (w : P ⟶ T) (t : W ⟶ T)
    [IsIso u] [IsIso m] [IsIso w]
    (hf : u ≫ m ≫ a = b ≫ v) (hn : q ≫ w = v ≫ t) :
    inv m ≫ inv u ≫ b ≫ q = a ≫ t ≫ inv w := by
  apply (cancel_mono w).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hn, ← Category.assoc b v t, ← hf]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_derived_adj_eq
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f =
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm := by
  exact Adjunction.derived_eq_ofNatIsoLeft
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactorsh.hom
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorUnit
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
      (upperStar (ModuleCat.{u + 1} A) f)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_mate_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fixedScalarRestrictionDirectImageMap φ f =
      (mateEquiv
        (Adjunction.mapDerivedCategoryRightDerivedAdjunction
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))
        (Adjunction.mapDerivedCategoryRightDerivedAdjunction
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (upperStarRestrictScalarsIso φ f)).hom)) := by
  change (mateEquiv
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (fixedScalarRestrictionPullback φ f).hom)) = _
  rw [restriction_derived_adj_eq, restriction_derived_adj_eq]
  refine (mate_left_iso _ _ _ _ (fixedScalarRestrictionPullback φ f).hom).trans ?_
  congr 2
  ext K
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Iso.symm_hom, Iso.symm_inv, fixedScalarRestrictionPullback,
    leftDerivedUpperStarRestrictScalarsIso_hom_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

section ScalarModels
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The coefficient mate intertwines the canonical chain-level right-derived units. -/
theorem fixedScalarRestrictionDirectImageMap_factors
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ) :
    (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorUnitQ K) ≫
      (fixedScalarRestrictionDirectImageMap φ f).app (DerivedCategory.Q.obj K) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactors.hom.app
          K) =
    (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
        (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (fixedScalarRestrictionDirectImageUnderived φ f).hom (.up ℤ)).app K) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorUnitQ
        (((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomologicalComplex
          (.up ℤ)).obj K) := by
  have h := derived_mate_factors
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarRestrictScalarsIso φ f) K
  have hm := NatTrans.congr_app (restriction_mate_eq φ f) (DerivedCategory.Q.obj K)
  unfold Functor.mapDerivedCategorySquareIso at hm
  erw [← hm] at h
  rw [restriction_underived_mate] at h
  simpa only [fixedScalarRestrictionDirectImageUnderived, Iso.refl_hom,
    chainDerivedUnit, Functor.rightDerivedFunctorUnitQ] using h

private noncomputable def scalarDiagram {C : Type (u + 1)} [Category.{u} C]
    (A : Type (u + 1)) [Ring A] :
    PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{u + 1} A) where
  obj M :=
    { obj W := M.obj W
      map f := ModuleCat.ofHom (M.map f).hom
      map_id W := by ext x; exact ConcreteCategory.congr_hom (M.map_id W) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (M.map_comp f g) x }
  map f :=
    { app W := f.app W
      naturality W W' a := by
        ext x
        exact ConcreteCategory.congr_hom (f.naturality a) x }
  map_id M := by ext W x; rfl
  map_comp f g := by ext W x; rfl
private noncomputable def scalarSections {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [Ring A]
    (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj) :
    SheafOfModules.{u + 1} R ⥤ Sheaf J (ModuleCat.{u + 1} A) where
  obj M :=
    ⟨(scalarDiagram A).obj ((PresheafOfModules.restrictScalars α).obj M.val),
      Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := ⟨(scalarDiagram A).map ((PresheafOfModules.restrictScalars α).map f.val)⟩
  map_id M := by ext W x; rfl
  map_comp f g := by ext W x; rfl

private theorem scalarUnitIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) {R₀ : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (R : Sheaf J RingCat.{u + 1}) (α : R₀ ⟶ R.obj)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (P : PresheafOfModules.{u + 1} R₀) (hP : Presheaf.IsSheaf J P.presheaf) :
    IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app P) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
  simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact isIso_toSheafify J hP

attribute [local irreducible] PresheafOfModules.sheafification
  PresheafOfModules.sheafificationAdjunction

private theorem scalarSections_isEquivalence {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [Ring A]
    (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    (scalarSections J A R α).IsEquivalence := by
  let E := sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ finiteCoefficientModulePresheaf C A ⋙
    PresheafOfModules.sheafification α
  have : E.IsEquivalence := coefficientRealization_isEquivalence J A R α
  let η : 𝟭 (Sheaf J (ModuleCat.{u + 1} A)) ⟶ E ⋙ scalarSections J A R α :=
    { app M := ⟨(scalarDiagram A).map
        ((PresheafOfModules.sheafificationAdjunction α).unit.app
          ((finiteCoefficientModulePresheaf C A).obj M.obj))⟩
      naturality M N f := by
        apply Sheaf.hom_ext
        exact congrArg (scalarDiagram A).map
          ((PresheafOfModules.sheafificationAdjunction α).unit.naturality
            ((finiteCoefficientModulePresheaf C A).map f.hom)) }
  have hη (M : Sheaf J (ModuleCat.{u + 1} A)) : IsIso (η.app M) := by
    have hP : Presheaf.IsSheaf J
        ((finiteCoefficientModulePresheaf C A).obj M.obj).presheaf := by
      have he : ((finiteCoefficientModulePresheaf C A).obj M.obj).presheaf =
          M.obj ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} := by
        apply CategoryTheory.Functor.ext
        · intro W W' f
          ext x
          rfl
        · intro W
          rfl
      rw [he]
      exact ((sheafCompose J
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M).property
    have hi := scalarUnitIso J R α ((finiteCoefficientModulePresheaf C A).obj M.obj) hP
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J (ModuleCat.{u + 1} A))]
    change IsIso ((scalarDiagram A).map
      ((PresheafOfModules.sheafificationAdjunction α).unit.app
        ((finiteCoefficientModulePresheaf C A).obj M.obj)))
    infer_instance
  have : IsIso η := NatIso.isIso_of_isIso_app η
  have : (E ⋙ scalarSections J A R α).IsEquivalence :=
    Functor.isEquivalence_of_iso (asIso η)
  exact Functor.isEquivalence_of_comp_left E (scalarSections J A R α)

private noncomputable abbrev scalarRing {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u + 1}]
    (A : Type (u + 1)) [CommRing A] :=
  (constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)
private noncomputable abbrev scalarRingUnderlying {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u + 1}]
    (A : Type (u + 1)) [CommRing A] :=
  (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (scalarRing J A)
private noncomputable def scalarUnit {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u + 1}]
    (A : Type (u + 1)) [CommRing A] :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ (scalarRingUnderlying J A).obj :=
  Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private theorem scalarUnit_inj {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u + 1}]
    [J.WEqualsLocallyBijective CommRingCat.{u + 1}]
    (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallyInjective J (scalarUnit J A) := by
  apply (Presheaf.isLocallyInjective_forget_iff J (scalarUnit J A)).mp
  change Presheaf.IsLocallyInjective J
    (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
      (forget CommRingCat.{u + 1}))
  infer_instance

private theorem scalarUnit_surj {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u + 1}]
    [J.WEqualsLocallyBijective CommRingCat.{u + 1}]
    (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallySurjective J (scalarUnit J A) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget J (scalarUnit J A)).mpr
  change Presheaf.IsLocallySurjective J
    (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
      (forget CommRingCat.{u + 1}))
  infer_instance

private noncomputable def scalarRestrictionIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (R S : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ S.obj) (a : R ⟶ S)
    (h : α ≫ a.hom = (Functor.const Cᵒᵖ).map (RingCat.ofHom φ) ≫ β) :
    SheafOfModules.restrictScalars a ⋙ scalarSections J A R α ≅
      scalarSections J B S β ⋙ Sheaf.restrictScalars J φ := by
  let L := SheafOfModules.restrictScalars a ⋙ scalarSections J A R α
  let T := scalarSections J B S β ⋙ Sheaf.restrictScalars J φ
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine
      { hom := ⟨{
          app := fun W ↦ ModuleCat.ofHom (X := (L.obj M).obj.obj W)
            (Y := (T.obj M).obj.obj W) {
            toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := ?_ }
          naturality := by intros; ext x; rfl }⟩
        inv := ⟨{
          app := fun W ↦ ModuleCat.ofHom (X := (T.obj M).obj.obj W)
            (Y := (L.obj M).obj.obj W) {
            toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := ?_ }
          naturality := by intros; ext x; rfl }⟩
        hom_inv_id := by ext W x; rfl
        inv_hom_id := by ext W x; rfl }
    · intro c x
      let x' : M.val.obj W := x
      change (a.hom.app W).hom ((α.app W).hom c) • x' = (β.app W).hom (φ c) • x'
      exact congrArg (fun r : S.obj.obj W ↦ r • x') (ConcreteCategory.congr_hom (congr_app h W) c)
    · intro c x
      let x' : M.val.obj W := x
      change (β.app W).hom (φ c) • x' = (a.hom.app W).hom ((α.app W).hom c) • x'
      exact congrArg (fun r : S.obj.obj W ↦ r • x')
        (ConcreteCategory.congr_hom (congr_app h W) c).symm
  · intros; ext W x; rfl
private noncomputable def inverseSquare
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E : C ⥤ C') (F : D ⥤ D') [E.IsEquivalence] [F.IsEquivalence]
    (r : C ⥤ D) (s : C' ⥤ D') (α : r ⋙ F ≅ E ⋙ s) :
    E.inv ⋙ r ≅ s ⋙ F.inv :=
  Functor.isoWhiskerLeft E.inv (Functor.isoWhiskerLeft r F.asEquivalence.unitIso) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft E.inv α) F.inv ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight E.asEquivalence.counitIso s) F.inv
private noncomputable def scalarDirectImageIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : D ⥤ C) [F.IsContinuous K J]
    (A : Type (u + 1)) [CommRing A]
    (R : Sheaf K RingCat.{u + 1}) (S : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Dᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ S.obj)
    (q : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} K J).obj S)
    (h : α ≫ q.hom = Functor.whiskerLeft F.op β) :
    SheafOfModules.pushforward q ⋙ scalarSections K A R α ≅
      scalarSections J A S β ⋙ F.sheafPushforwardContinuous (ModuleCat.{u + 1} A) K J := by
  let L := SheafOfModules.pushforward q ⋙ scalarSections K A R α
  let T := scalarSections J A S β ⋙
    F.sheafPushforwardContinuous (ModuleCat.{u + 1} A) K J
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine
      { hom := ⟨{
          app := fun W ↦ ModuleCat.ofHom (X := (L.obj M).obj.obj W)
            (Y := (T.obj M).obj.obj W) {
            toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := ?_ }
          naturality := by intros; ext x; rfl }⟩
        inv := ⟨{
          app := fun W ↦ ModuleCat.ofHom (X := (T.obj M).obj.obj W)
            (Y := (L.obj M).obj.obj W) {
            toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := ?_ }
          naturality := by intros; ext x; rfl }⟩
        hom_inv_id := by ext W x; rfl
        inv_hom_id := by ext W x; rfl }
    · intro c x
      let x' : M.val.obj (F.op.obj W) := x
      change (q.hom.app W).hom ((α.app W).hom c) • x' = (β.app (F.op.obj W)).hom c • x'
      exact congrArg (fun r : S.obj.obj (F.op.obj W) ↦ r • x')
        (ConcreteCategory.congr_hom (congr_app h W) c)
    · intro c x
      let x' : M.val.obj (F.op.obj W) := x
      change (β.app (F.op.obj W)).hom c • x' = (q.hom.app W).hom ((α.app W).hom c) • x'
      exact congrArg (fun r : S.obj.obj (F.op.obj W) ↦ r • x')
        (ConcreteCategory.congr_hom (congr_app h W) c).symm
  · intros; ext W x; rfl
private noncomputable abbrev scalarSectionsAt (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] :=
  scalarSections (Scheme.ProEt.topology X) A
    (scalarRingUnderlying (Scheme.ProEt.topology X) A)
    (scalarUnit (Scheme.ProEt.topology X) A)

private theorem scalarSectionsAt_equiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarSectionsAt X A).IsEquivalence := by
  have := scalarUnit_inj (Scheme.ProEt.topology X) A
  have := scalarUnit_surj (Scheme.ProEt.topology X) A
  exact scalarSections_isEquivalence _ _ _ _
private noncomputable def scalarChange (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    scalarRing (Scheme.ProEt.topology X) A ⟶ scalarRing (Scheme.ProEt.topology X) B :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)

private theorem scalarChange_unit (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    scalarUnit (Scheme.ProEt.topology X) A ≫
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarChange X φ)).hom =
    (Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫
      scalarUnit (Scheme.ProEt.topology X) B := by
  have h := toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom φ))
  exact congrArg (fun t ↦ Functor.whiskerRight t
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h.symm
private noncomputable def scalarPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (scalarRing (Scheme.ProEt.topology Y) A) ≅
      scalarRing (Scheme.ProEt.topology X) A := by
  letI : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have := finiteCoefficientCommRingMap_isIso f A
  exact asIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
    (CommRingCat.of A))

private theorem scalarDirectImage_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    scalarUnit (Scheme.ProEt.topology Y) A ≫
      Functor.whiskerRight (Scheme.proEtaleRingDirectImageMap f
        (scalarRing (Scheme.ProEt.topology Y) A) (scalarRing (Scheme.ProEt.topology X) A)
        (scalarPullbackIso f A)).hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (scalarUnit (Scheme.ProEt.topology X) A) := by
  have hr : Scheme.proEtaleRingDirectImageMap f
      (scalarRing (Scheme.ProEt.topology Y) A) (scalarRing (Scheme.ProEt.topology X) A)
      (scalarPullbackIso f A) =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) :=
    ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  rw [hr]
  have h := Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (scalarRing (Scheme.ProEt.topology X) A)))
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  exact congrArg (fun t ↦ Functor.whiskerRight t
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h

private theorem fixedRestriction_resolution_quasiIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ)
    [I.IsKInjective]
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ)
    [J.IsKInjective]
    (j : ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) := by
  let RX := scalarRing (Scheme.ProEt.topology X) A
  let SX := scalarRing (Scheme.ProEt.topology X) B
  let RY := scalarRing (Scheme.ProEt.topology Y) A
  let ax := scalarChange X φ
  let c := scalarPullbackIso f A
  let H := Sheaf.restrictScalars (Scheme.ProEt.topology X) φ
  let G := lowerStar (ModuleCat.{u + 1} A) f
  let r := Scheme.proEtaleRingRestrictScalars ax
  let p := Scheme.proEtaleRingModuleDirectImage f RY RX c
  have hEM : (scalarSectionsAt X B).IsEquivalence := scalarSectionsAt_equiv X B
  have hEA : (scalarSectionsAt X A).IsEquivalence := scalarSectionsAt_equiv X A
  have hEB : (scalarSectionsAt Y A).IsEquivalence := scalarSectionsAt_equiv Y A
  let EM := (scalarSectionsAt X B).inv
  let EA := (scalarSectionsAt X A).inv
  let EB := (scalarSectionsAt Y A).inv
  have : EM.IsEquivalence := inferInstance
  have : EA.IsEquivalence := inferInstance
  have : EB.IsEquivalence := inferInstance
  have : EM.Additive := EM.additive_of_preserves_binary_products
  have : EA.Additive := EA.additive_of_preserves_binary_products
  have : EB.Additive := EB.additive_of_preserves_binary_products
  have : EA.PreservesHomology := inferInstance
  have : EB.PreservesHomology := inferInstance
  have : EB.ReflectsIsomorphisms := inferInstance
  have : EM.PreservesKInjectiveComplexes := inferInstance
  have : EA.PreservesKInjectiveComplexes := inferInstance
  have : H.Additive := inferInstanceAs (Sheaf.restrictScalars _ φ).Additive
  have : G.Additive := inferInstanceAs (lowerStar (ModuleCat.{u + 1} A) f).Additive
  have : r.Additive := inferInstanceAs (Scheme.proEtaleRingRestrictScalars ax).Additive
  have : p.Additive := inferInstanceAs
    (Scheme.proEtaleRingModuleDirectImage f RY RX c).Additive
  let α₀ : r ⋙ scalarSectionsAt X A ≅ scalarSectionsAt X B ⋙ H :=
    scalarRestrictionIso (Scheme.ProEt.topology X) φ _ _ _ _ _ (scalarChange_unit X φ)
  let α : EM ⋙ r ≅ H ⋙ EA :=
    inverseSquare (scalarSectionsAt X B) (scalarSectionsAt X A) r H α₀
  let β₀ : p ⋙ scalarSectionsAt Y A ≅ scalarSectionsAt X A ⋙ G :=
    scalarDirectImageIso (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
      (Scheme.proEtaleBaseChange f) A _ _ _ _ _ (scalarDirectImage_unit f A)
  let β : EA ⋙ p ≅ G ⋙ EB :=
    inverseSquare (scalarSectionsAt X A) (scalarSectionsAt Y A) p G β₀
  apply Scheme.quasiIso_map_of_models EM EA EB r p H G α β ?_ I J j
  intro I' hI J' hJ j' hj
  have : I'.IsKInjective := hI
  have : J'.IsKInjective := hJ
  have : QuasiIso j' := hj
  exact Scheme.restriction_directImage_quasiIso f RY RX SX ax c I' J' j'

end ScalarModels

attribute [local irreducible] fixedScalarRestrictionDirectImageMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of finite coefficients commutes with the unbounded derived direct image.
The map is fixed by its adjunction-mate definition, rather than an arbitrary isomorphism. -/
theorem fixedScalarRestrictionDirectImageMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (fixedScalarRestrictionDirectImageMap φ f) := by
  apply derived_mate_isIso
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarRestrictScalarsIso φ f) (fixedScalarRestrictionDirectImageMap φ f)
    (𝟙 _) (restriction_mate_eq φ f) (restriction_underived_mate φ f)
  intro I hI J hJ j hj
  have : I.IsKInjective := hI
  have : J.IsKInjective := hJ
  have : QuasiIso j := hj
  exact fixedRestriction_resolution_quasiIso φ f I J j

/-- The forward-direction canonical comparison, with the K-injective normalization
inherited from the named mate theorem. -/
@[no_expose] noncomputable def fixedScalarRestrictionDirectImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) ≅
      R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ :=
  letI := fixedScalarRestrictionDirectImageMap_isIso φ f
  (asIso (fixedScalarRestrictionDirectImageMap φ f)).symm

/-- The inverse of the forward coefficient comparison is the derived mate. -/
theorem fixedScalarRestrictionDirectImage_inv
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (fixedScalarRestrictionDirectImage φ f).inv =
      fixedScalarRestrictionDirectImageMap φ f := by
  rfl

end AlgebraicGeometry.ProEtale

attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint
