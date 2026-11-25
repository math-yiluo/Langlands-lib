/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

lemma restrictedOverCohomologyMap_eq_rawAffine
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k) :
    restrictedOverCohomologyMap k F (p : ℤ) f U =
      rawAffineRestrictedCohomologyMap f.left (B.hom ≫ k) (A.hom ≫ k) w p
        (restrictedOverCoefficient F B) (restrictedOverCoefficient F A)
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app F) U := by
  rfl

end AlgebraicGeometry.Etale
