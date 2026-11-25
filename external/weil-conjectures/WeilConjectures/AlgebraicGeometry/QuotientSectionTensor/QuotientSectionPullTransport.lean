/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Logic.Small.Defs
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportExtension
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportComputed
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # A step of the normalized quotient section comparison

## References

* Stacks 03EL, 06YY, 0D6D and 0G7E
* Stacks 06YY, 0D6D and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Share the large inferred cochain structures while checking the diagram proof.
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

attribute [local semireducible] QuotientChange.L
attribute [local implicit_reducible] QuotientChange.L
  InternalAbelianSheafModule.sectionRingSheaf
  DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.catToReflQuiver
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

open ModuleRingedComparison

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The normalized section pullback comparison exists for the supplied endpoint models. -/
theorem section_pull_transport_section_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam) :
    ∃ barLam : cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T,
      SectionPullNormalized a f cX cY barLam := by
  obtain ⟨barLam, hflat⟩ := section_pull_transport_section_normalized_kflat
    a f cX cY hcX hcY lam hlam
  exact ⟨barLam, section_pull_transport_extend_kflat a f cX cY barLam hflat⟩

-- Reconcile the source module-object instances with the normalized section interfaces.
/-- The derived section comparison satisfies the pull condition once its normalized
counit square is fixed. -/
theorem section_pull_transport_condition_of_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T)
    (hnorm : SectionPullNormalized a f cX cY barLam) :
    PullSectionCondition a f cX cY lam barLam := by
  classical
  let source := (D a Y ⋙ L Λ' f) ⋙ derivedFunctor Λ' X
  let target := (derivedFunctor Λ Y ⋙ derivedPullback Λ f) ⋙ cX.model.T
  let θ₁ : source ⟶ target :=
    Functor.whiskerRight lam.hom (derivedFunctor Λ' X) ≫
      Functor.whiskerLeft (L Λ f) cX.derived.hom ≫
      Functor.whiskerRight (derivedPullComparison Λ f).hom cX.model.T
  let θ₂ : source ⟶ target :=
    Functor.whiskerLeft (D a Y) (derivedPullComparison Λ' f).hom ≫
      Functor.whiskerRight cY.derived.hom (derivedPullback Λ' f) ≫
      Functor.whiskerLeft (derivedFunctor Λ Y) barLam.hom
  intro M
  obtain ⟨H, hH, ⟨e⟩⟩ := CondensedRing.exists_kFlat_iso_Qh_obj Λ M
  have : (extension a Y).PreservesKFlatQuasiIso := by
    set_option backward.isDefEq.respectTransparency false in
      exact Mod.preservesKFlatQuasiIso (AlgebraicGeometry.ProEtale.coefficientMap a Y)
  have hε : IsIso ((scalarCounit a Y).app H) := by
    have := CondensedRing.isLeftDerivabilityStructure_localizerMorphismKFlat Λ Y
    unfold scalarCounit D
    exact (extension a Y).derives_kFlat.isIso_of_isLeftDerivedFunctor
      (extension a Y).leftDerivedFunctorCounit ⟨H, hH⟩
  have hq : θ₁.app (DerivedCategory.Qh.obj H) = θ₂.app (DerivedCategory.Qh.obj H) := by
    obtain ⟨P, hP⟩ := HomotopyCategory.quotient_obj_surjective H
    have : IsIso ((scalarCounit a Y).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
      rw [hP]
      exact hε
    rw [← hP]
    exact section_pull_transport_condition_on_computed a f cX cY hcX hcY lam hlam barLam hnorm P
  change θ₁.app M = θ₂.app M
  apply (cancel_epi (source.map e.hom)).mp
  rw [θ₁.naturality, θ₂.naturality, hq]

/-- The same normalized scalar models realize the specified scalar/pullback map. -/
theorem section_pull_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam) :
    ∃ barLam : cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T,
      PullSectionCondition a f cX cY lam barLam ∧
        SectionPullNormalized a f cX cY barLam   := by
  obtain ⟨barLam, hnorm⟩ := section_pull_transport_section_normalized
    a f cX cY hcX hcY lam hlam
  exact ⟨barLam, section_pull_transport_condition_of_normalized
    a f cX cY hcX hcY lam hlam barLam hnorm, hnorm⟩

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
