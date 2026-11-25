/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.Algebra.Category.ModuleCat.Adjunctions
import all Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.RingTheory.Flat.Stability
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-! # K-flat resolutions compatible with the coefficient-universe lift

Source: Stacks Project, more-algebra.tex, lemma-K-flat-resolution and remark-P-resolution.
-/

@[expose] public section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits

/-- A small complex admits a K-flat resolution which remains K-flat after lifting
both its ring and module carriers to the next universe.

Source: Stacks Project, more-algebra.tex, lemma-K-flat-resolution and
remark-P-resolution (the filtered-free resolution).
(blueprint: lem-weil-pbc-coefficient-lift-kflat-resolution).

Proof: choose a flat-term K-flat resolution in the original module universe.
The coefficient-lift functor is additive, preserves flat modules (universe lift
preserves flatness and restricting along the ring equivalence preserves flatness),
and preserves colimits indexed by the ordered integers. The latter follows by
forgetting to sets: the small module forgetful functor preserves filtered colimits,
the type-universe lift preserves colimits, and the larger module forgetful functor
reflects filtered colimits. Apply kFlat_map_of_flat_terms to this resolution.
That theorem proves preservation using a flat resolution and its acyclic flat-term
cone, bounded-above good truncations, and exact filtered colimits. Thus its tests
include all acyclic complexes in the larger universe. No bound on the original
complex is assumed, and the zero complex and zero ring are included. -/
theorem CochainComplex.exists_coefficientLift_kFlat_resolution
    {B : Type t} [CommRing B] (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    ∃ (R : CochainComplex (ModuleCat.{t} B) ℤ) (f : R ⟶ P),
      QuasiIso f ∧ R.IsKFlatForTotalTensor ∧
        CochainComplex.IsKFlatForTotalTensor
        (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
          ModuleCat.restrictScalars.{t + 1}
            (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapHomologicalComplex
              (.up ℤ)).obj R) := by
  classical
  have := ModuleCat.hasFunctorialFlatResolution_sameUniverse B
  let F := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  have : F.PreservesFlat := by
    constructor
    intro M hM
    have : Module.Flat B M := (ModuleCat.flat_iff_flat _).1 hM
    have : Module.Flat B (ULift.{t + 1} M) := inferInstance
    apply (ModuleCat.flat_iff_flat _).2
    change Module.Flat (ULift.{t + 1} B) (ULift.{t + 1} M)
    exact Module.Flat.ulift_left_iff.mpr this
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{t} B)) :=
    preservesFilteredColimitsOfSize_shrink _
  have : ReflectsFilteredColimitsOfSize.{0, 0}
      (forget (ModuleCat.{t + 1} (ULift.{t + 1} B))) :=
    reflectsFilteredColimitsOfSize_shrink _
  have : PreservesColimitsOfShape ℤ (F ⋙ forget (ModuleCat.{t + 1} (ULift.{t + 1} B))) := by
    change PreservesColimitsOfShape ℤ
      (forget (ModuleCat.{t} B) ⋙ CategoryTheory.uliftFunctor.{t + 1, t})
    infer_instance
  have : PreservesColimitsOfShape ℤ F :=
    preservesColimitsOfShape_of_reflects_of_preserves F
      (forget (ModuleCat.{t + 1} (ULift.{t + 1} B)))
  obtain ⟨R, f, hf, hflat, hR⟩ := P.exists_quasiIso_flat_kFlat
  exact ⟨R, f, hf, hR, F.kFlat_map_of_flat_terms R hR hflat⟩
