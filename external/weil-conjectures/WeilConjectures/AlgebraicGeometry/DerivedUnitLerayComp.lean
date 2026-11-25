/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.DerivedLerayComp

/-! # Coherence of the derived unit and Leray comparison -/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

private theorem derivedUnit_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (mapDerivedUpperStarLowerStarAdjunction A (g ≫ f)).unit.app K ≫
      (lowerStar A (g ≫ f)).rightDerivedFunctor.map
        ((Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
          (Functor.mapDerivedCategoryCompIso (upperStar A f)
            (upperStar A g)).symm).hom.app K) =
    (mapDerivedUpperStarLowerStarAdjunction A f).unit.app K ≫
      (lowerStar A f).rightDerivedFunctor.map
        ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app
          ((upperStar A f).mapDerivedCategory.obj K)) ≫
      (rightDerivedLowerStarComp A g f).hom.app
        ((upperStar A g).mapDerivedCategory.obj
          ((upperStar A f).mapDerivedCategory.obj K)) := by
  simpa only [rightDerivedLowerStarComp, Iso.symm_hom, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv, Adjunction.comp_unit_app, Category.assoc, Functor.comp_obj] using
    (unit_conjugateEquiv
      ((mapDerivedUpperStarLowerStarAdjunction A f).comp
        (mapDerivedUpperStarLowerStarAdjunction A g))
      (mapDerivedUpperStarLowerStarAdjunction A (g ≫ f))
      (Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar A f)
          (upperStar A g)).symm).hom K).symm

/-- The derived unit--Leray composites respect inverse-image composition.
Source: Stacks Project, Tags 015M and 03CB.
(blueprint: lem-weil-pbc-derived-unit-leray-comp).

Proof: Write U_f and U_g for the exact functors induced on derived categories, R_f and R_g for the
derived direct images, C:U_(g≫f)≅U_f followed by U_g for mapDerivedCategoryNatIso(upperStarComp)
followed by mapDerivedCategoryCompIso, and D:R_g followed by R_f≅R_(g≫f) for its conjugate. The
derived adjunction unit equation states eta_(g≫f),K followed by R_(g≫f)(C_K) equals eta_f,K
followed by R_f(eta_g,U_f(K)) followed by D_(U_g(U_f(K))). It is the unit-conjugation equation
for the adjunctions; the conjugate agrees with the canonical derived direct-image composition by
the right-derived comparison characterization.

The underived direct-image and terminal-section comparisons associate: evaluating an iterated
base change of the terminal object is the same as evaluating its composite base change, because
both isomorphisms commute with its projections. Deriving that equation yields RGamma_X(D_M)
followed by lambda_(g≫f),M equal to lambda_f,R_g(M) followed by lambda_g,M. Indeed both sides
precomposed with the composite right-derived unit are the localization of that underived
comparison. Direct image preserves K-injectives, so the composite right-derived functor has the
universal property, which makes these transformations equal.

Use naturality of lambda_(g≫f) at C_K to move RGamma_Z(C_K) across lambda_(g≫f). Substitute the
unit equation from step 1 and then the Leray composition equation from step 2, with
M=U_g(U_f(K)). The resulting composite contains RGamma_X(R_f(eta_g,U_f(K))) followed by
lambda_f,R_g(U_g(U_f(K))). Naturality of lambda_f at eta_g,U_f(K) replaces these by
lambda_f,U_f(K) followed by RGamma_Y(eta_g,U_f(K)). After reassociating, the result is exactly
the product of the unit-Leray composites for f at K and for g at U_f(K). -/
theorem derivedUnitLeray_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A (g ≫ f)).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A (g ≫ f)).hom.app
      ((upperStar A (g ≫ f)).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections A Z).map
      ((Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar A f)
          (upperStar A g)).symm).hom.app K) =
    (rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A f).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.app
      ((upperStar A f).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections A Y).map
      ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app
        ((upperStar A f).mapDerivedCategory.obj K)) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A g).hom.app
      ((upperStar A g).mapDerivedCategory.obj
        ((upperStar A f).mapDerivedCategory.obj K)) := by
  let C := Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar A f)
      (upperStar A g)).symm
  let U := (upperStar A f).mapDerivedCategory
  let V := (upperStar A g).mapDerivedCategory
  let R := (lowerStar A f).rightDerivedFunctor
  let G := rightDerivedGlobalSections A X
  let H := rightDerivedGlobalSections A Y
  let eta := (mapDerivedUpperStarLowerStarAdjunction A f).unit.app K
  let theta := (mapDerivedUpperStarLowerStarAdjunction A g).unit.app
    (U.obj K)
  let lambda := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    A f).hom
  let mu := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    A (g ≫ f)).hom
  have hn := mu.naturality (C.hom.app K)
  have hu := congrArg G.map (derivedUnit_comp f g K)
  have hl := derivedLeray_comp f g (V.obj (U.obj K))
  have ht := lambda.naturality theta
  dsimp only [Functor.comp_map] at hn ht
  change G.map _ ≫ mu.app _ ≫ _ =
    G.map eta ≫ lambda.app (U.obj K) ≫ H.map theta ≫ _
  rw [← hn, ← G.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [hl]
  change G.map eta ≫ G.map (R.map theta) ≫ lambda.app _ ≫ _ = _
  erw [reassoc_of% ht]

end AlgebraicGeometry.Etale
