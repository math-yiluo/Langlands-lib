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
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.HypercoverComplex
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Algebra.Homology.ComplexExtensionColimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Bounded-below filtered-colimit continuity of pro-etale hypercohomology

## Main definitions

- `ringHypercohomology`: integer-degree derived sections with arbitrary ring-sheaf coefficients.

## Main statements

- `ringHypercohomology_transport_preservesZeroMorphisms`: transport acts on complexes.
- `isIso_ringHypercohomology_colimitPost`: the canonical bounded-below continuity map is invertible.

## References

* Tag 03D1
* Stacks Project, Tags 079P and 09A2

## Implementation details

`ringHypercohomology` transports to the small site model by sectionwise precomposition. On
bounded-below complexes it agrees with evaluating a bounded-below injective resolution, since
both compute the right derived evaluation functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The sectionwise transport to the small site model preserves zero morphisms. -/
theorem ringHypercohomology_transport_preservesZeroMorphisms (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext V x
  rfl

attribute [instance] ringHypercohomology_transport_preservesZeroMorphisms

/-- Hypercohomology in degree `q` at an object of the small pro-etale site, with arbitrary
ring-sheaf coefficients: the homology of the sections of a functorial K-injective resolution,
computed on the small site model. -/
noncomputable def ringHypercohomology (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) (q : ℤ) :
    CochainComplex (ringedSiteModules.{u + 1} R) ℤ ⥤ AddCommGrpCat.{u + 1} :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    CochainComplex.kInjectiveResolutionFunctor.{u + 1} (ringedSiteModules.{u + 1} S) ⋙
    (SheafOfModules.evaluation S (op (AsSmall.up.obj U)) ⋙
      forget₂ (ModuleCat.{u + 1} (S.obj.obj (op (AsSmall.up.obj U))))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q

private noncomputable def moduleModelEquiv (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R) := by
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm.functor.IsContinuous
      (proEtaleModelTopology X) (topology X) :=
    inferInstanceAs ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsContinuous _ _)
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm.inverse.IsContinuous
      (topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm
    (𝟙 _) (𝟙 _) (by
      ext V x
      change (R.obj.map (𝟙 V)) x = x
      simp) (by
      ext V x
      change (R.obj.map (𝟙 (op (ULift.down V.unop)))) x = x
      simp)

end AlgebraicGeometry.Scheme.ProEt
