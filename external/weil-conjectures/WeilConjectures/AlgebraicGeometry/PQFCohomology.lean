/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Sheaf cohomology and higher direct images

Source: Stacks Project, Cohomology, Tag 01DZ, equations cohomology-modules and
higher-direct-image-modules; Tag 079W (blueprint: pqf-def-cohomology).
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The cohomology functors `H^p(X, -)` of a scheme are the recorded
`RingedSpace.moduleCohomology X.toRingedSpace p`, the right derived functors of global
sections on `𝒪_X`-modules (by definition). They form a cohomological δ-functor, so a short
exact sequence of `𝒪_X`-modules gives a long exact cohomology sequence. For a morphism
`f : X ⟶ S`, the higher direct image `R^p f_* F = H^p(Rf_*(F[0]))` is naturally isomorphic
to the `p`-th right derived functor of module direct image `f_*`.

Source: Stacks Project, Cohomology, Tag 01DZ, equations cohomology-modules and
higher-direct-image-modules; Tag 079W (blueprint: pqf-def-cohomology).

Proof:
1. Use def-sc-ringed-space-module-cohomology: an injective resolution followed by global
sections computes H^p, independently of the resolution, as the right derived functor.
2. Regard a scheme morphism as a morphism of ringed spaces. By
 def-pc-ringed-spaces-derived-direct-image, derived direct image is computed by applying
module direct image to a K-injective resolution. Enough injectives is supplied by
lem-sc-ringed-space-module-sheaves-enough-injectives. An injective resolution is bounded
below and hence K-injective by lem-weil-pbc-bounded-below-injectives-kinjective. Taking
p-th cohomology therefore computes the ordinary p-th right derived functor, naturally
in the module; comparison of resolutions gives the displayed functor isomorphism.
3. Global sections is additive and left exact (lem-sc-global-sections-left-exact;
sectionwise kernels and finite products give the same assertion for module-valued
sections). Apply lem-weil-pbc-right-derived-universal-delta-functor to obtain connecting
maps and exactness for every short exact sequence. The cohomological delta-functor
packages the initial monomorphism, all three repeating exactness positions, and
naturality. Its degree functors are the established moduleCohomology functors. -/
theorem sheafCohomologyAndHigherDirectImages (X : Scheme.{u}) :
    (∃ G : CohomologicalDeltaFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))),
      G.F = RingedSpace.moduleCohomology X.toRingedSpace) ∧
    ∀ (S : Scheme.{u}) (f : X ⟶ S)
      [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
      [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))] (p : ℕ),
      Nonempty ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0 ⋙
        RingedSpace.derivedModuleDirectImage f.toLRSHom.toShHom ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (p : ℤ)) ≅
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p) := by
  constructor
  · let : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) :=
      inferInstanceAs (PreservesFiniteLimits
        (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
    obtain ⟨G, hG, _, _⟩ :=
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).exists_universal_rightDerived_deltaFunctor
    exact ⟨G, hG⟩
  · intro S f _ _ p
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    exact ⟨Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (DerivedCategory.Plus.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0)
        F.rightDerivedFunctorPlusCompatibility.symm)
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (p : ℤ)) ≪≫
      F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p⟩

end AlgebraicGeometry
