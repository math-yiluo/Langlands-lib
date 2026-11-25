/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars

/-! # Coherence of etale coefficient normalization

Source: Stacks Project, Tags 03DA, 03ED and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem coefficients_eq {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    etaleNormalizationCoefficients f q =
      Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIso q f) := by
  unfold etaleNormalizationCoefficients
  congr 1

private theorem coefficients_comp {T Z Y : Scheme.{u}} (f : T ⟶ Z) (g : Z ⟶ Y)
    (k : T ⟶ Y) (h : k = f ≫ g)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (C : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))) :
    (etaleNormalizationCoefficients k q).hom.app C ≫
        (normalizationRestrict T.smallEtaleTopology q).map
          ((Functor.mapDerivedCategoryTriangleIso
            (Etale.upperStarComp (ModuleCat.{u + 1} S) f g k h)).hom.app C) =
      (Functor.mapDerivedCategoryTriangleIso
        (Etale.upperStarComp (ModuleCat.{u + 1} R) f g k h)).hom.app
          ((normalizationRestrict Y.smallEtaleTopology q).obj C) ≫
        (Etale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.map
          ((etaleNormalizationCoefficients g q).hom.app C) ≫
        (etaleNormalizationCoefficients f q).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} S) g).mapDerivedCategory.obj C) := by
  subst k
  simp only [coefficients_eq]
  exact Functor.mapDerivedCategorySquareIso_hom_app_comp
    (Etale.upperStarRestrictScalarsIso q g) (Etale.upperStarRestrictScalarsIso q f)
    (Etale.upperStarRestrictScalarsIso q (f ≫ g))
    (Etale.upperStarComp _ f g) (Etale.upperStarComp _ f g)
    (fun N ↦ by simpa using congr_app (Etale.upperStarRestrictScalarsIso_comp_hom q f g) N) C

/-- The canonical coefficient arrow commutes with successive etale inverse images.
This equation holds for arbitrary arrows; universality and towers are not required.

Source: Stacks Project, Tags 03DA, 03ED and 06YY.
(blueprint: lem-weil-pbc-etale-normalization-coherence).

Proof: identify the specified exact coefficient comparison with the source library's
upperStarRestrictScalarsIso. Apply its ordinary composition identity and the
exact-localization square-pasting theorem, retaining the specified equality of scheme
maps. This gives coefficient compatibility with localIsomorphismRestrictionComp.
Conjugate that equation by its two component isomorphisms, then use naturality on delta.
Functoriality and cancellation give the displayed inverse-compositor equation for every
arrow. No boundedness, coefficient finiteness, flatness or Tor-amplitude assumption
enters this argument; zero rings, zero complexes and empty schemes are included. -/
theorem etaleNormalization_coherence (Y : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {C : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {C' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (δ : C ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj C') :
    (∀ {U V : Y.Etale} (f : U ⟶ V),
      (localIsomorphismRestrictionComp Y R f).inv.app C ≫
          etaleIsomorphismNormalizationArrow Y q δ U =
        (Etale.upperStar (ModuleCat.{u + 1} R) f.left).mapDerivedCategory.map
            (etaleIsomorphismNormalizationArrow Y q δ V) ≫
          (etaleNormalizationCoefficients f.left q).hom.app
            ((localIsomorphismRestriction Y S V).obj C') ≫
          (normalizationRestrict U.left.smallEtaleTopology q).map
            ((localIsomorphismRestrictionComp Y S f).inv.app C')) := by
  intro U V f
  have hp := coefficients_comp f.left V.hom U.hom f.w.symm q C'
  change (etaleNormalizationCoefficients U.hom q).hom.app C' ≫
      (normalizationRestrict U.left.smallEtaleTopology q).map
        ((localIsomorphismRestrictionComp Y S f).hom.app C') =
    (localIsomorphismRestrictionComp Y R f).hom.app
      ((normalizationRestrict Y.smallEtaleTopology q).obj C') ≫ _ at hp
  have hi : (localIsomorphismRestrictionComp Y R f).inv.app
        ((normalizationRestrict Y.smallEtaleTopology q).obj C') ≫
        (etaleNormalizationCoefficients U.hom q).hom.app C' =
      (Etale.upperStar (ModuleCat.{u + 1} R) f.left).mapDerivedCategory.map
        ((etaleNormalizationCoefficients V.hom q).hom.app C') ≫
      (etaleNormalizationCoefficients f.left q).hom.app
        ((localIsomorphismRestriction Y S V).obj C') ≫
      (normalizationRestrict U.left.smallEtaleTopology q).map
        ((localIsomorphismRestrictionComp Y S f).inv.app C') := by
    apply (cancel_epi ((localIsomorphismRestrictionComp Y R f).hom.app
      ((normalizationRestrict Y.smallEtaleTopology q).obj C'))).mp
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% hp]
    simp only [← Functor.map_comp, Iso.hom_inv_id_app]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := (localIsomorphismRestrictionComp Y R f).inv.naturality δ
  dsimp only [Functor.comp_map] at hn
  change _ ≫ ((localIsomorphismRestriction Y R U).map δ ≫
    (etaleNormalizationCoefficients U.hom q).hom.app C') =
    (Etale.upperStar (ModuleCat.{u + 1} R) f.left).mapDerivedCategory.map
      ((localIsomorphismRestriction Y R V).map δ ≫
        (etaleNormalizationCoefficients V.hom q).hom.app C') ≫ _
  rw [← Category.assoc, ← hn, Category.assoc, hi]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme
