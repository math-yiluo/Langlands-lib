/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
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
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleImmersionAlgebraicLimitsOfUniverses

/-! # Closed inverse image and countable products in independent universes

## References

* Stacks Project, Tag 09AA
* Stacks Project, assertion (1)
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_over_proEtTopology
universe t u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Closed inverse image preserves countable products of abelian sheaves, with
independent universes for schemes and sections. -/
theorem proEtaleClosedAbelianProductsOfUniverses
    {X Z : Scheme.{t}} (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesLimitsOfShape (Discrete ℕ)
      (Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange i)
        AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z)) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : LocallySmall.{max u (t + 1)} Z.ProEt := ⟨fun _ _ ↦ inferInstance⟩
  let (F : X.ProEtᵒᵖ ⥤ RingCat.{max u (t + 1)}) :
      (proEtaleBaseChange i).op.HasLeftKanExtension F := by
    have : ∀ V : Z.ProEtᵒᵖ,
        HasColimitsOfShape (CostructuredArrow (proEtaleBaseChange i).op V)
          RingCat.{max u (t + 1)} :=
      fun _ ↦ hasColimitsOfShape_of_essentiallySmall.{max u (t + 1)} _ _
    infer_instance
  let : HasSheafify (ProEt.topology Z) RingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} Z.ProEt := essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  let L : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology Z) RingCat.{max u (t + 1)} :=
    Functor.sheafPullbackConstruction.sheafPullback
    (proEtaleBaseChange i) RingCat.{max u (t + 1)}
      (ProEt.topology X) (ProEt.topology Z)
  let aL := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange i) RingCat.{max u (t + 1)}
      (ProEt.topology X) (ProEt.topology Z)
  let B : Sheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology Z) AddCommGrpCat.{max u (t + 1)} :=
    Functor.sheafPullbackConstruction.sheafPullback
    (proEtaleBaseChange i) AddCommGrpCat.{max u (t + 1)}
      (ProEt.topology X) (ProEt.topology Z)
  let aB := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange i) AddCommGrpCat.{max u (t + 1)}
      (ProEt.topology X) (ProEt.topology Z)
  have h := proEtale_immersion_algebraicInverse_limits i L aL B aB
  exact h.2.preservesLimitsOfShape

end AlgebraicGeometry.Scheme
