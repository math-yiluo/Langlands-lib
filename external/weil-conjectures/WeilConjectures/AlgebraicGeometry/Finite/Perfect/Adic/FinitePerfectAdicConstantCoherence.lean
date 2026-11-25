/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars

/-! # Restriction coherence of the constant finite perfect transition

Source: Stacks Project, Tags 06YY, 09BV and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-normalization-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem coefficientMate_eq {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    etaleNormalizationCoefficients f q =
      Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIso q f) := by
  rfl

private theorem coefficientMate_comp {Y Z W : Scheme.{t}} (f : W ⟶ Z) (g : Z ⟶ Y)
    (h : W ⟶ Y) (hh : h = f ≫ g)
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S)) :
    (Etale.upperStarRestrictScalarsIso q h).hom.app M ≫
        (Sheaf.restrictScalars W.smallEtaleTopology q).map
          ((Etale.upperStarComp (ModuleCat.{t + 1} S) f g h hh).hom.app M) =
      (Etale.upperStarComp (ModuleCat.{t + 1} R) f g h hh).hom.app
          ((Sheaf.restrictScalars Y.smallEtaleTopology q).obj M) ≫
        (Etale.upperStar (ModuleCat.{t + 1} R) f).map
          ((Etale.upperStarRestrictScalarsIso q g).hom.app M) ≫
        (Etale.upperStarRestrictScalarsIso q f).hom.app
          ((Etale.upperStar (ModuleCat.{t + 1} S) g).obj M) := by
  subst h
  simpa using congr_app (Etale.upperStarRestrictScalarsIso_comp_hom q f g) M

private theorem derivedCoefficientMate_comp (Y : Scheme.{t})
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {U V : Y.Etale} (f : U ⟶ V)
    (D : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S))) :
    (etaleNormalizationCoefficients U.hom q).hom.app D ≫
        (normalizationRestrict U.left.smallEtaleTopology q).map
          ((localIsomorphismRestrictionComp Y S f).hom.app D) =
      (localIsomorphismRestrictionComp Y R f).hom.app
          ((normalizationRestrict Y.smallEtaleTopology q).obj D) ≫
        (Etale.upperStar (ModuleCat.{t + 1} R) f.left).mapDerivedCategory.map
          ((etaleNormalizationCoefficients V.hom q).hom.app D) ≫
        (etaleNormalizationCoefficients f.left q).hom.app
          ((localIsomorphismRestriction Y S V).obj D) := by
  rw [coefficientMate_eq, coefficientMate_eq, coefficientMate_eq]
  exact Functor.mapDerivedCategorySquareIso_hom_app_comp
    (Etale.upperStarRestrictScalarsIso q V.hom)
    (Etale.upperStarRestrictScalarsIso q f.left)
    (Etale.upperStarRestrictScalarsIso q U.hom)
    (Etale.upperStarComp (ModuleCat.{t + 1} R) f.left V.hom U.hom f.w.symm)
    (Etale.upperStarComp (ModuleCat.{t + 1} S) f.left V.hom U.hom f.w.symm)
    (coefficientMate_comp f.left V.hom U.hom f.w.symm q) D

private theorem normalizationArrow_eq (Y : Scheme.{t})
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {C : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} R))}
    {D : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S))}
    (d : C ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj D) (U : Y.Etale) :
    etaleIsomorphismNormalizationArrow Y q d U =
      (localIsomorphismRestriction Y R U).map d ≫
        (etaleNormalizationCoefficients U.hom q).hom.app D := by
  rfl

private theorem normalizationArrow_coherence (Y : Scheme.{t})
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {C : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} R))}
    {D : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} S))}
    (δ : C ⟶ (normalizationRestrict Y.smallEtaleTopology q).obj D)
    {U V : Y.Etale} (f : U ⟶ V) :
    (localIsomorphismRestrictionComp Y R f).inv.app C ≫
        etaleIsomorphismNormalizationArrow Y q δ U =
      (Etale.upperStar (ModuleCat.{t + 1} R) f.left).mapDerivedCategory.map
          (etaleIsomorphismNormalizationArrow Y q δ V) ≫
        (etaleNormalizationCoefficients f.left q).hom.app
          ((localIsomorphismRestriction Y S V).obj D) ≫
        (normalizationRestrict U.left.smallEtaleTopology q).map
          ((localIsomorphismRestrictionComp Y S f).inv.app D) := by
  apply (cancel_mono ((normalizationRestrict U.left.smallEtaleTopology q).map
    ((localIsomorphismRestrictionComp Y S f).hom.app D))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [normalizationArrow_eq, normalizationArrow_eq, Functor.map_comp]
  simp only [Category.assoc]
  erw [derivedCoefficientMate_comp Y q f D]
  erw [← reassoc_of% (localIsomorphismRestrictionComp Y R f).inv.naturality δ]
  erw [Iso.inv_hom_id_app_assoc (localIsomorphismRestrictionComp Y R f)]

/-- The explicit constant transition satisfies etale restriction coherence.

Source: Stacks Project, Tags 06YY, 09BV and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-normalization-coherence).

Proof: expand the two displayed arrows as the inverse-image coefficient mates of
the same normalized constant arrow. Naturality of the pullback mate, followed by
the composition law for etale inverse images, identifies both composites on each
etale source. The identity is checked before localization and therefore descends
to the derived categories. No universality or stalk argument is used here.
-/
theorem finitePerfectAdicEtaleConstant_coherence (Y : Scheme.{t})
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    ∀ {U V : Y.Etale} (f : U ⟶ V),
      (localIsomorphismRestrictionComp Y
          (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))) f).inv.app
          (finitePerfectAdicEtaleConstant Y T (n + 1)) ≫
        etaleIsomorphismNormalizationArrow Y
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
          (finitePerfectAdicEtaleConstantTransition Y T n) U =
      (Etale.upperStar (ModuleCat.{t + 1}
          (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) f.left).mapDerivedCategory.map
          (etaleIsomorphismNormalizationArrow Y
            (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
            (finitePerfectAdicEtaleConstantTransition Y T n) V) ≫
        (etaleNormalizationCoefficients f.left
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).hom.app
          ((localIsomorphismRestriction Y
            (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))) V).obj
            (finitePerfectAdicEtaleConstant Y T n)) ≫
        (normalizationRestrict U.left.smallEtaleTopology
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).map
          ((localIsomorphismRestrictionComp Y
            (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))) f).inv.app
            (finitePerfectAdicEtaleConstant Y T n)) := by
  intro U V f
  exact normalizationArrow_coherence Y
    (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
    (finitePerfectAdicEtaleConstantTransition Y T n) f

end AlgebraicGeometry.Scheme
