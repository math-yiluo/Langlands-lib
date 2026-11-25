/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Exact

/-!
# The derived unit of an exact compactification sheaf functor

Source: Stacks Project, Tags 0GKM and 015F
(blueprint: def-sfb-exact-compactification-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (a : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
    lowerStar (ModuleCat.{u + 1} A) c.g)

/-- Descend the sheaf comparison followed by the proper direct-image derived unit.
The descent is unique because precomposition with the homotopy localization is fully faithful.
Source: Stacks Project, Tags 0GKM and 015F
(blueprint: def-sfb-exact-compactification-unit). -/
@[irreducible]
noncomputable def exactCompactificationUnit :
    F.mapDerivedCategory ⟶
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  normalizationLocalizationDesc DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
    (F := F.mapDerivedCategory)
    (G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (F.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (a.hom.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory (.up ℤ))
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactorsh.inv
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom)

/-- For a finite compactification the derived unit is invertible on all complexes:
finite direct image is exact, so every factor in the displayed representative is invertible.
Full faithfulness of localization reflects this isomorphism.
Source: Stacks Project, Tags 0GKM and 015F
(blueprint: lem-sfb-exact-compactification-unit-finite). -/
theorem isIso_exactCompactificationUnit_of_isFinite [IsFinite c.g] :
    IsIso (exactCompactificationUnit A c F a) := by
  have ha : IsIso (a.hom.mapHomotopyCategory (.up ℤ)) :=
    ⟨a.inv.mapHomotopyCategory (.up ℤ),
      by rw [← NatTrans.mapHomotopyCategory_comp, a.hom_inv_id,
        NatTrans.mapHomotopyCategory_id],
      by rw [← NatTrans.mapHomotopyCategory_comp, a.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]⟩
  unfold exactCompactificationUnit normalizationLocalizationDesc
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ)) _).preimageIso
      (asIso _) |>.isIso_hom

end AlgebraicGeometry.Etale
