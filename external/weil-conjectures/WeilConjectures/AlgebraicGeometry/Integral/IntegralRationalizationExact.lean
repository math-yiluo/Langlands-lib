/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleMonodromyRealizationData
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.RingTheory.RingHom.Flat

set_option linter.privateModule false

/-! # Exact rationalization of integral continuous coefficient modules

## References

* Bhatt--Scholze, Lemma 6.8.2(2)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open scoped ChangeOfRings

open CategoryTheory CategoryTheory.Limits Opposite

namespace SfScalarExtension
variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} (α : A ⟶ B)
set_option hygiene false in
local notation "R" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
set_option hygiene false in
local notation "S" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj B
set_option hygiene false in
local notation "a" => (sheafCompose J (forget₂ CommRingCat RingCat)).map α

private noncomputable def P : SheafOfModules.{u} R ⥤ PresheafOfModules.{u} (S).obj where
  obj M := SheafOfModules.changeOfRingsPresheaf α M
  map f := { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
             naturality := SheafOfModules.changeOfRingsHom_naturality α _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id _
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp _ _

@[irreducible] private noncomputable def F (α : A ⟶ B) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} S :=
  P α ⋙ PresheafOfModules.sheafification (𝟙 (S).obj)

private theorem preserves (hflat : ∀ U : Cᵒᵖ, (α.hom.app U).hom.Flat) :
    PreservesFiniteLimits (F α) := by
  have hP : PreservesFiniteLimits (P α) := by
    constructor
    intro D _ _
    constructor
    intro K
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hflat U)
    exact isLimitOfPreserves (ModuleCat.extendScalars (α.hom.app U).hom)
      (isLimitOfPreserves (SheafOfModules.evaluation R U) (limit.isLimit K))
  unfold F
  exact comp_preservesFiniteLimits (P α) (PresheafOfModules.sheafification (𝟙 (S).obj))

end SfScalarExtension

namespace AlgebraicGeometry.Scheme

open Topology

private theorem continuous_denominator {K : Type u} [NormedField K]
    [IsUltrametricDist K] {X : Type v} [TopologicalSpace X]
    (A : Subring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1) (f : C(X, K)) :
    ∃ (a s : C(X, A)),
      (∀ x, (s x : K) ≠ 0) ∧ (∀ x, f x * (s x : K) = (a x : K)) := by
  classical
  let D : Set X := {x | ‖f x‖ ≤ 1}
  have hD : IsClopen D := by
    have h := (IsUltrametricDist.isClopen_closedBall (x := (0 : K))
      (by norm_num : (1 : ℝ) ≠ 0)).preimage f.continuous
    simpa only [D, Set.preimage_ofPred_eq, Metric.closedBall, dist_zero_right] using h
  let s₀ : X → K := D.piecewise (fun _ ↦ 1) (fun x ↦ (f x)⁻¹)
  have hs₀ : Continuous s₀ := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ D
    · have hloc : s₀ =ᶠ[nhds x] fun _ ↦ (1 : K) := by
        filter_upwards [hD.isOpen.mem_nhds hx] with y hy
        exact Set.piecewise_eq_of_mem D _ _ hy
      exact continuousAt_const.congr_of_eventuallyEq hloc
    · have hfx : f x ≠ 0 := by
        intro hz
        apply hx
        change ‖f x‖ ≤ 1
        simp [hz]
      have hloc : s₀ =ᶠ[nhds x] fun y ↦ (f y)⁻¹ := by
        filter_upwards [hD.compl.isOpen.mem_nhds hx] with y hy
        exact Set.piecewise_eq_of_notMem D _ _ hy
      exact (f.continuous.continuousAt.inv₀ hfx).congr_of_eventuallyEq hloc
  have hsA (x : X) : s₀ x ∈ A := by
    rw [hA]
    dsimp [s₀, Set.piecewise]
    split_ifs with hx
    · simp
    · rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hx))
  let s : C(X, A) := ⟨fun x ↦ ⟨s₀ x, hsA x⟩, hs₀.subtype_mk _⟩
  have haA (x : X) : f x * s₀ x ∈ A := by
    rw [hA]
    dsimp [s₀, Set.piecewise]
    split_ifs with hx
    · simpa only [mul_one] using (show ‖f x‖ ≤ 1 from hx)
    · have hfx : f x ≠ 0 := by
        intro hz
        apply hx
        change ‖f x‖ ≤ 1
        simp [hz]
      simp [hfx]
  let a : C(X, A) := ⟨fun x ↦ ⟨f x * s₀ x, haA x⟩,
    (f.continuous.mul hs₀).subtype_mk _⟩
  refine ⟨a, s, ?_, fun _ ↦ rfl⟩
  intro x
  change s₀ x ≠ 0
  dsimp [s₀, Set.piecewise]
  split_ifs with hx
  · exact one_ne_zero
  · apply inv_ne_zero
    intro hz
    apply hx
    change ‖f x‖ ≤ 1
    simp [hz]

private theorem continuous_localization {K : Type u} [NormedField K]
    [IsUltrametricDist K] {X : Type v} [TopologicalSpace X]
    (A : Subring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1) :
    let φ : C(X, A) →+* C(X, K) :=
      A.subtype.compLeftContinuous X continuous_subtype_val
    letI := φ.toAlgebra
    IsLocalization ((IsUnit.submonoid C(X, K)).comap φ) C(X, K) := by
  dsimp only
  let φ : C(X, A) →+* C(X, K) := A.subtype.compLeftContinuous X continuous_subtype_val
  let := φ.toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨fun s ↦ s.property, ?_, ?_⟩
  · intro f
    obtain ⟨a, s, hs, ha⟩ := continuous_denominator A hA f
    refine ⟨⟨a, ⟨s, ?_⟩⟩, ?_⟩
    · exact ⟨⟨φ s, ⟨fun x ↦ (φ s x)⁻¹, s.continuous.subtype_val.inv₀ hs⟩,
        by ext x; exact mul_inv_cancel₀ (hs x),
        by ext x; exact inv_mul_cancel₀ (hs x)⟩, rfl⟩
    · ext x
      exact ha x
  · intro a b hab
    have he : a = b := by
      ext x
      exact DFunLike.congr_fun hab x
    exact ⟨1, by simp [he]⟩

private theorem continuous_flat {K : Type u} [NormedField K]
    [IsUltrametricDist K] {X : Type v} [TopologicalSpace X]
    (A : Subring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1) :
    (A.subtype.compLeftContinuous X continuous_subtype_val).Flat := by
  let φ : C(X, A) →+* C(X, K) := A.subtype.compLeftContinuous X continuous_subtype_val
  let := φ.toAlgebra
  have := continuous_localization A hA (X := X)
  exact IsLocalization.flat C(X, K) ((IsUnit.submonoid C(X, K)).comap φ)

end AlgebraicGeometry.Scheme
