/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Exact constant-coefficient restriction and upper cohomological bounds

## References

* Stacks Project, Tag 03D2
* Stacks Project, Tag 0735, termwise exact inverse image
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical constant-coefficient restriction functor. -/
noncomputable def proEtaleConstantModulePullbackFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) :=
  have := constantComparison_isIso f A
  proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (asIso (proEtaleCoefficientInverseImageMap f A))

/-- Additivity of the canonical restriction functor. -/
instance proEtaleConstantModulePullbackFunctor_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] : (proEtaleConstantModulePullbackFunctor f A).Additive := by
  unfold proEtaleConstantModulePullbackFunctor
  infer_instance

/-- Left exactness of the canonical restriction functor. -/
instance proEtaleConstantModulePullbackFunctor_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    PreservesFiniteLimits (proEtaleConstantModulePullbackFunctor f A) := by
  unfold proEtaleConstantModulePullbackFunctor
  infer_instance

/-- Right exactness of the canonical restriction functor. -/
instance proEtaleConstantModulePullbackFunctor_preservesFiniteColimits
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    PreservesFiniteColimits (proEtaleConstantModulePullbackFunctor f A) := by
  unfold proEtaleConstantModulePullbackFunctor
  infer_instance

/-- Exact constant-coefficient pullback commutes with cohomology. -/
noncomputable def proEtaleConstantModulePullbackHomologyIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A]
    (K : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ) (i : ℤ) :
    ((proEtaleConstantModulePullbackFunctor f A).mapHomologicalComplex
      (ComplexShape.up ℤ) |>.obj K).homology i ≅
        proEtaleConstantModulePullback f A
          ((DerivedCategory.homologyFunctor (proEtaleRingModules Y
            (proEtaleConstantRing Y A)) i).obj (DerivedCategory.Q.obj K)) :=
  (K.sc i).mapHomologyIso (proEtaleConstantModulePullbackFunctor f A) ≪≫
    (proEtaleConstantModulePullbackFunctor f A).mapIso
      ((DerivedCategory.homologyFunctorFactors _ i).app K).symm

/-- Upper cohomological bounds survive the canonical constant-coefficient restriction. -/
theorem proEtaleConstantModulePullback_boundedAbove {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A]
    (K : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
    (hK : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
      ((DerivedCategory.homologyFunctor (proEtaleRingModules Y
        (proEtaleConstantRing Y A)) j).obj (DerivedCategory.Q.obj K))) :
    ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
      (((proEtaleConstantModulePullbackFunctor f A).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj K).homology j) := by
  obtain ⟨b, hb⟩ := hK
  refine ⟨b, fun j hj ↦ ?_⟩
  exact ((proEtaleConstantModulePullbackFunctor f A).map_isZero (hb j hj)).of_iso
    (proEtaleConstantModulePullbackHomologyIso f A K j)

end AlgebraicGeometry.Scheme
