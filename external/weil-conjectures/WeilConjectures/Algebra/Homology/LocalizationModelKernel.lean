/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizationModelSemilinear
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.BaseTensorUnitCohomologyModel
import WeilConjectures.Algebra.Homology.ComplexLocalizationUnitKernel

/-! # Torsion kernel of the canonical localization cohomology map

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-first-localization-cohomology-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A Aq B D : Type u)
  [CommRing R] [CommRing A] [CommRing Aq] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- A cohomology class killed by the localization unit is killed by a denominator.
Source: Stacks Project, Tags 06Y6 and 0DJ8; exactness of localization.
(blueprint: lem-pc-first-localization-cohomology-kernel).

Proof: choose a K-flat R-resolution F of B[0]. Its tensor with Q computes the
balanced derived tensor. Localization in A is exact and commutes with the direct
sums of this total complex, so a class that becomes a boundary after localization
has a representative whose multiple by some s in S is a boundary already before
localization. This follows by clearing the finitely many denominators of the
cycle representative and the boundary witness in the adjacent degrees; equivalently
apply exactness of localized modules to cycles modulo boundaries. Compare the
balanced computation with L and K using the unique universal-counit comparisons.
Their naturality identifies the class map with localizationModelMap, and their
scalar compatibility identifies multiplication by s with includeLeft s. Transport
the torsion equation to L. If zero lies in S take s=0; for S={1} the map is the
model-comparison isomorphism and its kernel is zero. -/
theorem localizationModelMap_kernel
    (S : Submonoid A) [IsLocalization S Aq] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
    (x : L.cohomology i)
    (hx : localizationModelMap R A Aq B D i Q L K uQ x = 0) :
    ∃ s : S, (Algebra.TensorProduct.includeLeft (S := R) (s : A) : A ⊗[R] B) • x = 0 :=
  by
    obtain ⟨C, e, e', he⟩ :=
      exists_baseTensorUnitCohomologyModel R A Aq B D i Q L K uQ huQ
    have hzero : (HomologicalComplex.homologyMap
        (((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
          (.up ℤ)).unit.app C) i) (e.hom x) = 0 := by
      rw [← he x, hx]
      exact e'.hom.hom.map_zero
    obtain ⟨s, hs⟩ := complexLocalizationUnit_kernel A Aq S i C (e.hom x) hzero
    refine ⟨s, ?_⟩
    apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
    exact (e.hom.hom.map_smul (s : A) x).trans (hs.trans e.hom.hom.map_zero.symm)

end RingTensorCohomology
