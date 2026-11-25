/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage

set_option linter.privateModule false

/-!
# Coefficient cocycle of the normalized pro-etale derived direct image

Source: Stacks Project, derived.tex, Tag 070Y (`lemma-K-injective-defined`), and the
agent-written coefficient-composition argument in the DAG
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle).

The comparisons are the specified `fixedScalarRestrictionDirectImage` isomorphisms.
The restriction associators are the existing sectionwise identity isomorphisms localized
termwise as `Sheaf.derivedRestrictScalarsCompIso`. All derived categories are unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

-- The coefficient-chain calculation uses only exact localization and adjunctions.
/-- Mates preserve a pasted coefficient square: transpose along the final adjunction and use
its counit, naturality, and the two individual mate identities.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem mate_chain
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {P : A ⥤ B} {Q : B ⥤ A} (adj : Q ⊣ P)
    {P' : C ⥤ D} {Q' : D ⥤ C} (adj' : Q' ⊣ P')
    {P'' : E ⥤ F} {Q'' : F ⥤ E} (adj'' : Q'' ⊣ P'')
    {S : B ⥤ D} {S' : A ⥤ C} {T : D ⥤ F} {T' : C ⥤ E}
    {U : B ⥤ F} {U' : A ⥤ E}
    (α : S ⋙ Q' ⟶ Q ⋙ S') (β : T ⋙ Q'' ⟶ Q' ⋙ T')
    (γ : U ⋙ Q'' ⟶ Q ⋙ U') (c : S ⋙ T ≅ U) (c' : S' ⋙ T' ≅ U')
    (hγ : ∀ M : B, γ.app M = Q''.map (c.inv.app M) ≫ β.app (S.obj M) ≫
      T'.map (α.app M) ≫ c'.hom.app (Q.obj M)) (K : A) :
    (mateEquiv adj adj'' (TwoSquare.mk _ _ _ _ γ)).app K =
      c.inv.app (P.obj K) ≫ T.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α)).app K) ≫
        (mateEquiv adj' adj'' (TwoSquare.mk _ _ _ _ β)).app (S'.obj K) ≫
        P''.map (c'.hom.app K) := by
  apply (adj''.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [adj''.counit_naturality]
  rw [mateEquiv_counit]
  rw [reassoc_of% (mateEquiv_counit adj' adj'' (TwoSquare.mk _ _ _ _ β) (S'.obj K)), hγ]
  simp only [Category.assoc]
  dsimp only [TwoSquare.mk]
  erw [β.naturality_assoc]
  simp only [Functor.comp_map]
  slice_rhs 3 4 => rw [← T'.map_comp, mateEquiv_counit, T'.map_comp]
  simp only [Category.assoc]
  rw [← c'.hom.naturality]
  rfl

/-- Exact localization preserves coefficient pasting. Apply the square-composition API to
the inverse squares and cancel the comparison isomorphisms.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem derive_chain
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type (u + 1)}
    [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂]
    [Category.{u} B₀] [Category.{u} B₁] [Category.{u} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂]
    [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory.{u} A₀] [HasDerivedCategory.{u} A₁] [HasDerivedCategory.{u} A₂]
    [HasDerivedCategory.{u} B₀] [HasDerivedCategory.{u} B₁] [HasDerivedCategory.{u} B₂]
    (R₁₀ : A₁ ⥤ A₀) (R₂₁ : A₂ ⥤ A₁) (R₂₀ : A₂ ⥤ A₀)
    (U₁₀ : B₁ ⥤ B₀) (U₂₁ : B₂ ⥤ B₁) (U₂₀ : B₂ ⥤ B₀)
    (Q₀ : A₀ ⥤ B₀) (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂)
    [R₁₀.Additive] [R₂₁.Additive] [R₂₀.Additive]
    [U₁₀.Additive] [U₂₁.Additive] [U₂₀.Additive]
    [Q₀.Additive] [Q₁.Additive] [Q₂.Additive]
    [PreservesFiniteLimits R₁₀] [PreservesFiniteColimits R₁₀]
    [PreservesFiniteLimits R₂₁] [PreservesFiniteColimits R₂₁]
    [PreservesFiniteLimits R₂₀] [PreservesFiniteColimits R₂₀]
    [PreservesFiniteLimits U₁₀] [PreservesFiniteColimits U₁₀]
    [PreservesFiniteLimits U₂₁] [PreservesFiniteColimits U₂₁]
    [PreservesFiniteLimits U₂₀] [PreservesFiniteColimits U₂₀]
    [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
    [PreservesFiniteLimits Q₁] [PreservesFiniteColimits Q₁]
    [PreservesFiniteLimits Q₂] [PreservesFiniteColimits Q₂]
    (e₀₁ : R₁₀ ⋙ Q₀ ≅ Q₁ ⋙ U₁₀) (e₁₂ : R₂₁ ⋙ Q₁ ≅ Q₂ ⋙ U₂₁)
    (e₀₂ : R₂₀ ⋙ Q₀ ≅ Q₂ ⋙ U₂₀)
    (r : R₂₁ ⋙ R₁₀ ≅ R₂₀) (t : U₂₁ ⋙ U₁₀ ≅ U₂₀)
    (he : ∀ M, e₀₂.hom.app M = Q₀.map (r.inv.app M) ≫
      e₀₁.hom.app (R₂₁.obj M) ≫ U₁₀.map (e₁₂.hom.app M) ≫ t.hom.app (Q₂.obj M))
    (M : DerivedCategory A₂) :
    (Functor.mapDerivedCategorySquareIso e₀₂).hom.app M =
      Q₀.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso R₂₁ R₁₀ ≪≫
          Functor.mapDerivedCategoryNatIso r).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso e₀₁).hom.app (R₂₁.mapDerivedCategory.obj M) ≫
      U₁₀.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso e₁₂).hom.app M) ≫
      (Functor.mapDerivedCategoryCompIso U₂₁ U₁₀ ≪≫
        Functor.mapDerivedCategoryNatIso t).hom.app (Q₂.mapDerivedCategory.obj M) := by
  have hi (N : A₂) : e₀₂.inv.app N ≫ Q₀.map (r.inv.app N) =
      t.inv.app (Q₂.obj N) ≫ U₁₀.map (e₁₂.inv.app N) ≫ e₀₁.inv.app (R₂₁.obj N) := by
    let z := Q₀.mapIso (r.symm.app N) ≪≫ e₀₁.app (R₂₁.obj N) ≪≫
      U₁₀.mapIso (e₁₂.app N) ≪≫ t.app (Q₂.obj N)
    have hz : e₀₂.app N = z := Iso.ext (he N)
    have hh := congrArg Iso.inv hz
    dsimp only [z, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv] at hh
    rw [hh]
    simp only [Category.assoc, ← Q₀.map_comp, Iso.hom_inv_id_app, Q₀.map_id,
      Category.comp_id]
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    e₁₂.symm e₀₁.symm e₀₂.symm t.symm r.symm hi M
  apply (cancel_epi ((Functor.mapDerivedCategorySquareIso e₀₂).inv.app M)).1
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom,
    Iso.trans_inv, NatTrans.comp_app, Category.assoc, Iso.symm_inv] at h ⊢
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

/-- Transport coefficient pasting along three natural isomorphisms. Naturality moves
the source associator past the first comparison; the intermediate inverses cancel.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem transport_chain
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (R₁₀ : A₁ ⥤ A₀) (R₂₁ : A₂ ⥤ A₁) (R₂₀ : A₂ ⥤ A₀)
    (U₁₀ : B₁ ⥤ B₀) (U₂₁ : B₂ ⥤ B₁) (U₂₀ : B₂ ⥤ B₀)
    {Q₀ q₀ : A₀ ⥤ B₀} {Q₁ q₁ : A₁ ⥤ B₁} {Q₂ q₂ : A₂ ⥤ B₂}
    (a₀ : Q₀ ≅ q₀) (a₁ : Q₁ ≅ q₁) (a₂ : Q₂ ≅ q₂)
    (e₀₁ : R₁₀ ⋙ q₀ ≅ q₁ ⋙ U₁₀) (e₁₂ : R₂₁ ⋙ q₁ ≅ q₂ ⋙ U₂₁)
    (e₀₂ : R₂₀ ⋙ q₀ ≅ q₂ ⋙ U₂₀)
    (r : R₂₁ ⋙ R₁₀ ≅ R₂₀) (t : U₂₁ ⋙ U₁₀ ≅ U₂₀)
    (he : ∀ M, e₀₂.hom.app M = q₀.map (r.inv.app M) ≫
      e₀₁.hom.app (R₂₁.obj M) ≫ U₁₀.map (e₁₂.hom.app M) ≫ t.hom.app (q₂.obj M))
    (M : A₂) :
    (Functor.isoWhiskerLeft R₂₀ a₀ ≪≫ e₀₂ ≪≫
      Functor.isoWhiskerRight a₂.symm U₂₀).hom.app M = Q₀.map (r.inv.app M) ≫
    (Functor.isoWhiskerLeft R₁₀ a₀ ≪≫ e₀₁ ≪≫
      Functor.isoWhiskerRight a₁.symm U₁₀).hom.app (R₂₁.obj M) ≫
    U₁₀.map ((Functor.isoWhiskerLeft R₂₁ a₁ ≪≫ e₁₂ ≪≫
      Functor.isoWhiskerRight a₂.symm U₂₁).hom.app M) ≫ t.hom.app (Q₂.obj M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (a₀.hom.naturality (r.inv.app M)), he]
  slice_rhs 4 5 => rw [← U₁₀.map_comp, Iso.inv_hom_id_app, U₁₀.map_id]
  simp only [Category.assoc]
  rw [← t.hom.naturality]
  simp only [Functor.comp_map]
  erw [Category.id_comp]

namespace AlgebraicGeometry.ProEtale

/-- The ordinary pullback/scalar comparison satisfies the adjunction unit identity,
since its supplied ordinary mate is the identity on direct images.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem e_unit {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).map ((upperStarRestrictScalarsIso φ f).hom.app M) =
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app M) := by
  have h := unit_mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom) M
  have hm := restriction_underived_mate φ f
  rw [hm] at h
  simpa using h.symm

/-- Ordinary scalar-pullback comparisons compose. Transpose along the pullback
adjunction, use the unit identity twice, and compare sectionwise identity associators.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem e_chain {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C)) :
    (upperStarRestrictScalarsIso (ψ.comp φ) f).hom.app M =
      (upperStar (ModuleCat.{u + 1} A) f).map
        ((Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl).inv.app M) ≫
      (upperStarRestrictScalarsIso φ f).hom.app
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ).obj M) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map
        ((upperStarRestrictScalarsIso ψ f).hom.app M) ≫
      (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl).hom.app
        ((upperStar (ModuleCat.{u + 1} C) f).obj M) := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [e_unit]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.naturality_assoc]
  erw [reassoc_of% (e_unit φ f ((Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ).obj M))]
  change _ = _ ≫ (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ).obj M)) ≫
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
      ((lowerStar (ModuleCat.{u + 1} B) f).map
        ((upperStarRestrictScalarsIso ψ f).hom.app M)) ≫ _
  rw [← Functor.map_comp_assoc, e_unit]
  ext U x
  rfl

/-- Localize the ordinary coefficient chain termwise and transport to the specified
derived pullbacks; no preservation of K-injectives is used.
Source: the coefficient-pasting argument of
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle). -/
private theorem scalarRestriction_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C))) :
    (leftDerivedUpperStarRestrictScalarsIso.{u} (ψ.comp φ) f).hom.app M =
      ((Functor.leftDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
        (upperStar.{u + 2, u} (ModuleCat.{u + 1} A) f))).map
        ((Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology X) rfl
          (f := φ) (g := ψ)).inv.app M) ≫
      (leftDerivedUpperStarRestrictScalarsIso.{u} φ f).hom.app
        ((Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) ψ).obj M) ≫
      (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ).map
        ((leftDerivedUpperStarRestrictScalarsIso.{u} ψ f).hom.app M) ≫
      (Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology T) rfl
        (f := φ) (g := ψ)).hom.app (((Functor.leftDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1,
          u + 1}
        (upperStar.{u + 2, u} (ModuleCat.{u + 1} C) f))).obj M) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact @transport_chain.{u + 2, u + 2, u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} C)))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) ψ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) (ψ.comp φ))
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) ψ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) (ψ.comp φ))
    _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory.{u + 2, u} (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory.{u + 2, u} (ModuleCat.{u + 1} B) f)
    (leftDerivedUpperStarIsoMapDerivedCategory.{u + 2, u} (ModuleCat.{u + 1} C) f)
    (Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (upperStarRestrictScalarsIso φ f))
    (Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (upperStarRestrictScalarsIso ψ f))
    (Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (upperStarRestrictScalarsIso (ψ.comp
        φ) f))
    (Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology X) rfl)
    (Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology T) rfl)
    (derive_chain.{u + 1}
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) (ψ.comp φ))
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) ψ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) (ψ.comp φ))
      (upperStar.{u + 2, u} (ModuleCat.{u + 1} A) f)
      (upperStar.{u + 2, u} (ModuleCat.{u + 1} B) f)
      (upperStar.{u + 2, u} (ModuleCat.{u + 1} C) f)
      (upperStarRestrictScalarsIso φ f) (upperStarRestrictScalarsIso ψ f)
      (upperStarRestrictScalarsIso (ψ.comp φ) f)
      (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl)
      (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl)
      (e_chain φ ψ f)) M

end AlgebraicGeometry.ProEtale
