/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeMapBridge
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeRawNaturality
import all WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

lemma restrictedOverCohomologyMap_raw_naturality
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k)
    (x : restrictedOverCohomology k F (p : ℤ) B U)
    (z : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) p
      (restrictedOverCoefficient F B)).obj (op U))
    (z' : (abelianHigherDirectImageRawPresheaf (A.hom ≫ k) p
      (restrictedOverCoefficient F A)).obj (op U))
    (hz : rawRestrictedCohomologyComparison (B.hom ≫ k) p
      (restrictedOverCoefficient F B) U z = x)
    (hz' : z' = abelianHigherDirectImageRawPullback f.left
      (B.hom ≫ k) (A.hom ≫ k) w p
      (restrictedOverCoefficient F B) (restrictedOverCoefficient F A)
      ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
        (Over.w f).symm).inv.app F) U z) :
    restrictedOverCohomologyMap k F (p : ℤ) f U x =
      rawRestrictedCohomologyComparison (A.hom ≫ k) p
        (restrictedOverCoefficient F A) U z' := by
  rw [restrictedOverCohomologyMap_eq_rawAffine k F p f U w]
  exact rawRestrictedComparison_naturality_chosen_at_x f.left
    (B.hom ≫ k) (A.hom ≫ k) w p
    (restrictedOverCoefficient F B) (restrictedOverCoefficient F A)
    ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
      (Over.w f).symm).inv.app F) U z z' x hz hz'

lemma restrictedOverCohomologyMap_raw_naturality_from_preimage
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k)
    (x : restrictedOverCohomology k F (p : ℤ) B U)
    (z : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) p
      (restrictedOverCoefficient F B)).obj (op U))
    (hz : rawRestrictedCohomologyComparison (B.hom ≫ k) p
      (restrictedOverCoefficient F B) U z = x) :
    restrictedOverCohomologyMap k F (p : ℤ) f U x =
      rawRestrictedCohomologyComparison (A.hom ≫ k) p
        (restrictedOverCoefficient F A) U
        (abelianHigherDirectImageRawPullback f.left
          (B.hom ≫ k) (A.hom ≫ k) w p
          (restrictedOverCoefficient F B) (restrictedOverCoefficient F A)
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app F) U z) := by
  exact restrictedOverCohomologyMap_raw_naturality
    k F p f U w x z _ hz rfl

lemma restrictedOverCohomologyMap_raw_naturality_canonical
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    [IsIso (rawRestrictedCohomologyComparison (B.hom ≫ k) p
      (restrictedOverCoefficient F B) U)]
    (w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k)
    (x : restrictedOverCohomology k F (p : ℤ) B U) :
    restrictedOverCohomologyMap k F (p : ℤ) f U x =
      rawRestrictedCohomologyComparison (A.hom ≫ k) p
        (restrictedOverCoefficient F A) U
        (abelianHigherDirectImageRawPullback f.left
          (B.hom ≫ k) (A.hom ≫ k) w p
          (restrictedOverCoefficient F B) (restrictedOverCoefficient F A)
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app F) U
          ((asIso (rawRestrictedCohomologyComparison (B.hom ≫ k) p
            (restrictedOverCoefficient F B) U)).inv x)) := by
  exact restrictedOverCohomologyMap_raw_naturality_from_preimage
    k F p f U w x _
    (Iso.inv_hom_id_apply
      (asIso (rawRestrictedCohomologyComparison (B.hom ≫ k) p
        (restrictedOverCoefficient F B) U)) x)

end AlgebraicGeometry.Etale
