/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeComp
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarCoherence

set_option linter.privateModule false

/-!
# Actual unbounded open adjunctions and site-comparison counits

Source: Stacks Project, Tags 03DI, 03DJ and 09AF; blueprint
sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md,
Locality paragraph (blueprint: lem-sp-unbounded-open-counit-site-transport).

The sheaf adjunctions are the specified Kan-extension/sheafification adjunctions.
`Adjunction.mapHomologicalComplex` gives their actual degreewise units and counits,
`Adjunction.mapHomotopyCategory` descends them to homotopy categories, and
`Adjunction.mapDerivedCategoryAdjunction` gives their unbounded derived adjunctions.
Its normalization on localized representatives is recorded in the imported
`Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj` and counit counterpart.
Thus no independent adjunction or comparison is selected here.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

-- Transposing both sides reduces counit compatibility to the two right triangles.
end CategoryTheory

namespace CategoryTheory.Functor

-- Uniqueness of right derived transformations compares the two inclusion paths.
private lemma normalized_identity_compat {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ C) [F.Additive] (ε : F ≅ 𝟭 C)
    (E : F.rightDerivedFunctor ≅ 𝟭 (_root_.DerivedCategory C))
    (h : ∀ K : HomotopyCategory C (.up ℤ),
      F.rightDerivedFunctorUnit.app K ≫ E.hom.app (_root_.DerivedCategory.Qh.obj K) =
        _root_.DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ε.hom (.up ℤ)).app K))
    (K : _root_.DerivedCategory.Plus C) :
    F.rightDerivedFunctorPlusCompatibility.hom.app K ≫ E.hom.app K.obj =
      _root_.DerivedCategory.Plus.ι.map
        ((rightDerivedFunctorPlusNatIso ε ≪≫ rightDerivedFunctorPlusIdIso C).hom.app K) := by
  have he : F.rightDerivedFunctorPlusCompatibility.hom ≫
      whiskerLeft _root_.DerivedCategory.Plus.ι E.hom =
      whiskerRight (rightDerivedFunctorPlusNatIso ε ≪≫ rightDerivedFunctorPlusIdIso C).hom
        _root_.DerivedCategory.Plus.ι := by
    apply rightDerived_ext (F.rightDerivedFunctorPlus ⋙ _root_.DerivedCategory.Plus.ι)
      F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C)
    ext M
    have hc : _root_.DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app M) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app
          (_root_.DerivedCategory.Plus.Qh.obj M) =
        F.rightDerivedFunctorUnit.app M.obj := by
      simpa [rightDerivedFunctorPlusCompatibility, rightDerivedFunctorPlusιUnit,
        ιRightDerivedFunctorUnit] using
        NatTrans.congr_app (rightDerivedNatTrans_fac
          (F.rightDerivedFunctorPlus ⋙ _root_.DerivedCategory.Plus.ι)
          (_root_.DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
          F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
          (HomotopyCategory.Plus.quasiIso C) (𝟙 _)) M
    dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      rightDerivedFunctorPlusιUnit]
    erw [← Category.assoc, hc, h, ← map_comp]
    erw [rightDerivedFunctorPlusUnit_app_comp_natIso_trans_idIso_hom_app]
    rfl
  exact NatTrans.congr_app he K

-- The exact-derived identity map has the same unit normalization.
end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
