/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm
import all WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero

/-!
# The canonical compact-support restriction comparison

Source: Stacks Tags 0GL5, 0GL6 and 0D6E; blueprint
(blueprint: lem-sf-compact-support-restriction-of-scalars).
All categories are the standard fixed-scalar presentation of modules over the constant ring.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The exact open adjunction, with the published derived pullback as right adjoint.
Source: Stacks Tag 03S2
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def fixedScalarOpenAdjunction (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    D((j)_!open[ModuleCat.{u + 1} A]) ⊣ L((j)^*[ModuleCat.{u + 1} A]) :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm

/-- Open extension and scalar restriction, normalized by the unit of the open adjunction.
It is the inverse mate of the actual restriction/pullback isomorphism.
Source: Stacks Tags 03S2 and 07A6
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionOpenMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        D((j)_!open[ModuleCat.{u + 1} A]) ⟶
      D((j)_!open[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ :=
  (mateEquiv (fixedScalarOpenAdjunction B j) (fixedScalarOpenAdjunction A j)).symm
    (fixedScalarRestrictionPullback φ j).inv

/-- The mate of `upperStarRestrictScalarsIso` along the pullback/pushforward adjunctions is the
identity of `g_* ⋙ Res = Res ⋙ g_*`, both being computed sectionwise.
Source: Stacks Tag 07A6 (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
theorem mateEquiv_upperStarRestrictScalarsIso_hom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom)) =
        TwoSquare.mk _ _ _ _ (𝟙 (lowerStar (ModuleCat.{u + 1} B) f ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ)) := by
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) φ)).injective
  apply NatTrans.ext
  funext M
  rw [iterated_mateEquiv_conjugateEquiv, conjugateEquiv_upperStarRestrictScalarsIso_hom]
  ext ⟨U⟩ x
  exact congrArg (fun t ↦ t.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
      _).symm

/-- Along an open immersion, `upperStarRestrictScalarsIso` is the identity of the restrictions,
read through the identifications of the pullbacks with the restrictions.
Source: Stacks Tags 03DI and 07A6 (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
theorem upperStarRestrictScalarsIso_hom_app_comp_of_isOpenImmersion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} B)) :
    (upperStarRestrictScalarsIso φ j).hom.app G ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
          ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j).hom.app G) =
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app
        ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj G) := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _).injective
  have h := unit_mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ j).hom) G
  rw [mateEquiv_upperStarRestrictScalarsIso_hom] at h
  simp only [TwoSquare.mk, NatTrans.id_app, Functor.id_obj] at h
  erw [Category.comp_id] at h
  have hA : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj G) ≫
      (j)_*[ModuleCat.{u + 1} A].map
        ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app
          ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj G)) =
      (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).map
        ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j).unit.app G) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  have hB : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j).unit.app G ≫
      (j)_*[ModuleCat.{u + 1} B].map
        ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j).hom.app G) =
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j).unit.app G :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  refine Eq.trans ?_ ((Adjunction.homEquiv_unit _ _ _ _).trans hA).symm
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← h, ← hB, Functor.map_comp]
  rfl

/-- The pullback along an open immersion is the restriction, and the extension-by-zero
adjunctions are transported along this identification.
Source: Stacks Tag 03DI (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
theorem openImmersionLowerShriekUpperStarAdjunction_eq (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j =
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm :=
  rfl

/-- The underived open comparison: the inverse mate of `upperStarRestrictScalarsIso` along the
extension-by-zero adjunctions is invertible.
Source: Stacks Tags 03DI and 0GL6 (blueprint: lem-sf-compact-support-restriction-of-scalars).
Proof: through the identification of the pullbacks with the restrictions, it is the inverse
mate of the identity square of restrictions, which is invertible. -/
theorem isIso_mateEquiv_symm_upperStarRestrictScalarsIso_inv
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso ((mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).symm
        (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ j).inv)) := by
  have h : (mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).symm
        (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ j).inv) =
      (mateEquiv (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)).symm
          (TwoSquare.mk _ _ _ _ (eqToHom rfl)) := by
    rw [openImmersionLowerShriekUpperStarAdjunction_eq,
      openImmersionLowerShriekUpperStarAdjunction_eq, mateEquiv_symm_ofNatIsoRight]
    congr 1
    refine NatTrans.ext (funext fun G ↦ ?_)
    have hc := upperStarRestrictScalarsIso_hom_app_comp_of_isOpenImmersion φ j G
    simp only [TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.symm_hom, Iso.symm_inv]
    erw [← hc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    rfl
  rw [h]
  exact scalarMap_isIso φ j

/-- Restriction commutes with the exact extension by zero.
Source: Stacks Tags 03S2 and 0GL6
(blueprint: lem-sf-compact-support-restriction-of-scalars).
Proof: on sheaves both composites have the same underlying extension-by-zero groups,
restriction maps and scalar actions. The identity on these groups is an isomorphism.
Its transpose is restriction of the unit of the open adjunction, hence it is exactly
the inverse mate displayed above. The equality descends termwise because all open
functors and restriction of scalars are exact. -/
theorem fixedScalarRestrictionOpenMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (fixedScalarRestrictionOpenMap φ j) := by
  have := isIso_mateEquiv_symm_upperStarRestrictScalarsIso_inv φ j
  let β := asIso ((mateEquiv
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).symm
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ j).inv))
  have hunit := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (upperStarRestrictScalarsIso φ j).symm β
    (fun K ↦ (unit_mateEquiv_symm
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ j).inv) K).symm)
  have hmate := mateEquiv_eq_of_unit
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B)
      j).mapDerivedCategoryAdjunction
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      j).mapDerivedCategoryAdjunction
    (Functor.mapDerivedCategorySquareIso β).hom
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso φ j).symm).hom
    (fun K ↦ (hunit K).symm)
  have h := (mateEquiv_ofNatIsoRight
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B)
      j).mapDerivedCategoryAdjunction
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      j).mapDerivedCategoryAdjunction
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm
    (Functor.mapDerivedCategorySquareIso β).hom)
  rw [hmate] at h
  have heq : fixedScalarRestrictionOpenMap φ j = (Functor.mapDerivedCategorySquareIso β).hom := by
    refine ((mateEquiv _ _).symm_apply_eq).2 (NatTrans.ext (funext fun K ↦ ?_))
    rw [fixedScalarOpenAdjunction, fixedScalarOpenAdjunction, NatTrans.congr_app h K]
    simp [fixedScalarRestrictionPullback, leftDerivedUpperStarRestrictScalarsIso,
      Functor.mapDerivedCategorySquareIso_symm]
  rw [heq]
  infer_instance

/-- The canonical open comparison, with its unit normalization.
Source: Stacks Tag 0GL6 (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionOpen
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  letI := fixedScalarRestrictionOpenMap_isIso φ j
  asIso (fixedScalarRestrictionOpenMap φ j)

/-- The specified proper/open composite, in the forward restriction direction.
Source: Stacks Tags 0GL5 and 0GL6
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def compactSupportRestrictionIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        Rf_!(c)[ModuleCat.{u + 1} A] ≅
      Rf_!(c)[ModuleCat.{u + 1} B] ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fixedScalarRestrictionOpen φ c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (fixedScalarRestrictionDirectImage φ c.g) ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale
