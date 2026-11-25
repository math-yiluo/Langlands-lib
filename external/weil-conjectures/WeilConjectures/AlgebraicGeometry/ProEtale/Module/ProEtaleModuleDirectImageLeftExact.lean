/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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

/-!
# Left exactness of pro-etale module direct image

## References

* Stacks Project, Tags 03DA and 03DC, first paragraph
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Direct image of constant-ring module sheaves on the small pro-etale sites is
additive and left exact. In these abelian categories, preservation of finite limits
is equivalent to preserving exact sequences `0 → F' → F → F''`. -/
theorem proEtaleConstantModuleDirectImage_additive_leftExact
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] :
    (proEtaleConstantModuleDirectImage f A).Additive ∧
      PreservesFiniteLimits (proEtaleConstantModuleDirectImage f A) := by
  constructor
  · constructor
    intro M N a b
    ext U x
    rfl
  · let RX := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)
    let RY := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)
    have : PreservesFiniteLimits
        (proEtaleConstantModuleDirectImage f A ⋙ SheafOfModules.toSheaf RY) := by
      -- Forgetting the scalar actions identifies pushforward with precomposition.
      change PreservesFiniteLimits (SheafOfModules.toSheaf RX ⋙
        (proEtaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X))
      infer_instance
    -- The forgetful functor preserves finite limits and reflects isomorphisms.
    exact preservesFiniteLimits_of_reflects_of_preserves
      (proEtaleConstantModuleDirectImage f A) (SheafOfModules.toSheaf RY)

end AlgebraicGeometry.Scheme
