/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality

-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem rawRestrictedComparison_naturality_chosen
    {S Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S)
    (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F') (U : S.Etale)
    (t : (abelianHigherDirectImageRawPresheaf h p F).obj (op U))
    (t' : (abelianHigherDirectImageRawPresheaf h' p F').obj (op U))
    (ht' : t' = abelianHigherDirectImageRawPullback a h h' w p F F' φ U t) :
    rawAffineRestrictedCohomologyMap a h h' w p F F' φ U
        (rawRestrictedCohomologyComparison h p F U t) =
      rawRestrictedCohomologyComparison h' p F' U t' := by
  subst t'
  exact rawRestrictedCohomologyComparison_naturality a h h' w p F F' φ U t

private theorem rawRestrictedComparison_naturality_chosen_at_x
    {S Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S)
    (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F') (U : S.Etale)
    (t : (abelianHigherDirectImageRawPresheaf h p F).obj (op U))
    (t' : (abelianHigherDirectImageRawPresheaf h' p F').obj (op U))
    (x : rawAffineRestrictedCohomology h p F U)
    (hx : rawRestrictedCohomologyComparison h p F U t = x)
    (ht' : t' = abelianHigherDirectImageRawPullback a h h' w p F F' φ U t) :
    rawAffineRestrictedCohomologyMap a h h' w p F F' φ U x =
      rawRestrictedCohomologyComparison h' p F' U t' := by
  rw [← hx]
  exact rawRestrictedComparison_naturality_chosen a h h' w p F F' φ U t t' ht'

end AlgebraicGeometry.Etale
