/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransportData
import all WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs

/-! # The fixed-coefficient open scalar comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
attribute [local irreducible] AlgebraicGeometry.ProEtale.localizationLowerShriekAdjunction

namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

private theorem scalar_unit_of_open_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {JA : C ⥤ D} {RA : D ⥤ C} {JB : E ⥤ F} {RB : F ⥤ E}
    {SX : C ⥤ E} {RX : E ⥤ C} {SZ : D ⥤ F} {RZ : F ⥤ D}
    (a : JA ⊣ RA) (b : JB ⊣ RB) (x : SX ⊣ RX) (z : SZ ⊣ RZ)
    (r : RB ⋙ RX ≅ RZ ⋙ RA) (q : RX ⋙ JA ⟶ JB ⋙ RZ)
    (hq : ∀ N, a.unit.app (RX.obj N) ≫ RA.map (q.app N) =
      RX.map (b.unit.app N) ≫ r.hom.app (JB.obj N)) (K : C) :
    z.homEquiv _ _
        (((a.comp z).leftAdjointUniq ((x.comp b).ofNatIsoRight r)).hom.app K) =
      JA.map (x.unit.app K) ≫ q.app (SX.obj K) := by
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← reassoc_of% (a.unit.naturality (x.unit.app K)), hq]
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (a.comp z) ((x.comp b).ofNatIsoRight r) K
  simpa only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.comp_obj, Category.assoc] using h

private theorem fixed_upper_unit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app
        ((sfFixedRestriction X φ).obj N) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
        ((sfFixedOpenRestriction j φ).hom.app N) =
    (sfFixedRestriction X φ).map
        ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).unit.app N) ≫
      (ProEtale.OpenScalarSite.restrictScalarsIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) j).hom.app
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).obj N) := by
  let ea := ProEtale.upperStarIsoOpenImmersionRestriction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let eb := ProEtale.upperStarIsoOpenImmersionRestriction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j
  change ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app
        ((sfFixedRestriction X φ).obj N) ≫ ea.inv.app _) ≫ _ =
    (sfFixedRestriction X φ).map
      ((ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).unit.app N ≫ eb.inv.app _) ≫ _
  have hn := ea.inv.naturality ((sfFixedOpenRestriction j φ).hom.app N)
  dsimp only [Functor.comp_obj] at hn
  simp only [ProEtale.OpenScalarSite.restrictScalarsIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Functor.map_comp,
    Category.assoc]
  erw [Category.id_comp]
  rw [← hn, ← Category.assoc, fixed_normalized]
  simp only [ea, eb, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem etale_open_iso_eq
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Etale.FiniteCompactScalar.openScalarIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) j =
      Etale.openScalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) j := by
  have he : (Etale.openRestrictScalarsIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) j).symm =
      Etale.upperStarRestrictScalarsIsoSheaf (RingHom.ulift.{u + 1, u + 1, u, u} φ) j :=
    Iso.ext (Etale.openRestrictScalarsIso_inv_eq (RingHom.ulift.{u + 1, u + 1, u, u} φ) j)
  have hd : (Functor.mapDerivedCategorySquareIso
        (Etale.openRestrictScalarsIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) j)).symm =
      Functor.mapDerivedCategorySquareIso
        (Etale.upperStarRestrictScalarsIsoSheaf (RingHom.ulift.{u + 1, u + 1, u, u} φ) j) :=
    Iso.ext (Etale.derived_square_symm (RingHom.ulift.{u + 1, u + 1, u, u} φ) j he)
  unfold Etale.FiniteCompactScalar.openScalarIso Etale.openScalarExtension
  rw [← hd]
  rfl

/-- Change of site preserves the fixed-coefficient open scalar mate.

Source: Stacks Tags 03DI and 09AF; the site part of Step 2 of
lem-finite-open-scalar-transport. (blueprint: lem-finite-open-scalar-site-transport).

Proof: the right adjoints of the open/site composites are restriction along
identical composites of site inclusions. Coefficient restriction commutes with
these restrictions sectionwise. The site/coefficient comparison is the mate
of that identity square; so is the site/open comparison. Paste this commuting
cube and take the scalar mates. The mate of the fixed open/coefficient square
is the displayed scalar transpose. On the etale face, uniqueness of the left
adjoint of open restriction followed by coefficient restriction gives precisely
openScalarIso. Exact termwise localization preserves the open/site and
coefficient restriction squares and their mate unit equations. Thus the two
pasted scalar mates agree on every unbounded derived object. This argument
uses neither a proper map nor intrinsic coefficient realization. -/
theorem fixedOpenScalar_site_transport
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (G : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X) :
    (((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology Z)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)))).homEquiv _ _).symm
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.map
            (((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology X)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)))).unit.app
              ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj G)) ≫
          (Functor.mapDerivedCategorySquareIso (sfFixedOpenRestriction j φ)).hom.app
            ((ProEtale.pbcFixedScalarExtension (ProEt.topology X)
              (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj
              ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj G))) ≫
      (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory.map
        ((ProEtale.pbcComparisonReduction X (RingHom.ulift.{u + 1, u + 1, u, u} φ)).hom.app G) =
    (ProEtale.pbcFixedScalarExtension (ProEt.topology Z) (RingHom.ulift.{u + 1, u + 1, u, u} φ)).map
        ((Functor.mapDerivedCategorySquareIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).inv.app G) ≫
      (ProEtale.pbcComparisonReduction Z (RingHom.ulift.{u + 1, u + 1, u, u} φ)).hom.app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj G) ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Z).mapDerivedCategory.map
        ((Etale.FiniteCompactScalar.openScalarIso
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) j).hom.app G) ≫
      (Functor.mapDerivedCategorySquareIso
        (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)).hom.app
        ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj G) := by
  let a := ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let b := ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j
  let x := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (ProEt.topology X) (RingHom.ulift.{u + 1, u + 1, u, u} φ))
  let z := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (ProEt.topology Z) (RingHom.ulift.{u + 1, u + 1, u, u} φ))
  let r := Functor.mapDerivedCategorySquareIso
    (ProEtale.OpenScalarSite.restrictScalarsIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) j)
  let q := (Functor.mapDerivedCategorySquareIso (sfFixedOpenRestriction j φ)).hom
  have hq := Adjunction.mapDerivedCategoryAdjunction_mate
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
    (ProEtale.OpenScalarSite.restrictScalarsIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) j)
    (sfFixedOpenRestriction j φ) (fixed_upper_unit φ j)
  have hn := scalar_unit_of_open_unit a b x z r q hq
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj G)
  have hm : (z.homEquiv _ _).symm
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.map
            (x.unit.app _) ≫ q.app _) =
      (ProEtale.OpenScalarSite.scalarOpen (RingHom.ulift.{u + 1, u + 1, u, u} φ) j).hom.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj G) := by
    apply (z.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact hn.symm
  dsimp only [ProEtale.pbcFixedScalarExtension, sfFixedRestriction,
    Sheaf.derivedRestrictScalars] at hm ⊢
  rw [hm]
  have h := ProEtale.OpenScalarSite.scalar_site_square_aux
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) j G
  rw [← etale_open_iso_eq φ j] at h
  have h' := congrArg (fun t ↦
    (ProEtale.pbcFixedScalarExtension (ProEt.topology Z) (RingHom.ulift.{u + 1, u + 1, u, u} φ)).map
      ((ProEtale.mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).inv.app G) ≫ t) h
  dsimp only [ProEtale.pbcFixedScalarExtension, Sheaf.derivedRestrictScalars] at h'
  simp only [ProEtale.mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp] at h'
  exact h'

end AlgebraicGeometry.Scheme.FiniteCompactScalar
