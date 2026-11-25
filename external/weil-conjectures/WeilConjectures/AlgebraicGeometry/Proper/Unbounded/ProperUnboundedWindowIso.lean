/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Proper.ProperIndConstructibleUnbounded
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedSums
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# The window isomorphisms for proper direct image

The schemes and morphism have the standing separated finite-type setting over a
positive-characteristic field, as in the amplitude theorem.

The two canonical arrows are asserted to be isomorphisms in the ambient module category.
All three objects are also asserted to be ind-constructible. Since the subcategory of
ind-constructible modules is full, this is exactly the assertion that these arrows are
isomorphisms there.

The dimension bound uses all nonnegative integers below the extended Krull dimension.
It expresses dim <= d for an integer d, including negative d and empty geometric fibres,
without converting d to a natural number and thereby losing the empty-fibre case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem dimension_bound (z : WithBot ℕ∞) (d : ℤ)
    (h : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ z → (n : ℤ) ≤ d) :
    z ≤ if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥ := by
  split_ifs with hd
  · by_contra hz
    have hn : ((d.toNat + 1 : ℕ) : WithBot ℕ∞) ≤ z := by
      exact ENat.WithBot.add_one_le_iff.mpr (lt_of_not_ge hz)
    have := h (d.toNat + 1) hn
    omega
  · have hz : z = ⊥ := by
      by_contra hz
      have hzero : (0 : WithBot ℕ∞) ≤ z := by
        rcases z with _ | z
        · exact (hz rfl).elim
        · exact WithBot.coe_le_coe.mpr zero_le
      have := h 0 hzero
      omega
    simp [hz]

private theorem window_maps_of_bounds
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (K : DerivedCategory C) (q d : ℤ)
    (hB : (F.obj ((DerivedCategory.TStructure.t.truncGE (q + 1)).obj K)).IsGE (q + 1))
    (hL : (F.obj ((DerivedCategory.TStructure.t.truncLE (q - 2 * d - 2)).obj
      ((DerivedCategory.TStructure.t.truncLE q).obj K))).IsLE (q - 1)) :
    IsIso ((DerivedCategory.homologyFunctor D q).map
      (F.map ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor D q).map
      (F.map ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
        ((DerivedCategory.TStructure.t.truncLE q).obj K)))) := by
  have hT := F.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished q (q + 1) rfl K)
  have hS := F.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished
      (q - 2 * d - 2) (q - 2 * d - 1) (by omega)
      ((DerivedCategory.TStructure.t.truncLE q).obj K))
  constructor
  · exact DerivedCategory.isIso_homologyMap_mor₁ _ hT (q - 1) q (by omega)
      ((DerivedCategory.isGE_iff _ _).mp hB (q - 1) (by omega))
      ((DerivedCategory.isGE_iff _ _).mp hB q (by omega))
  · exact DerivedCategory.isIso_homologyMap_mor₂ _ hS q (q + 1) rfl
      ((DerivedCategory.isLE_iff _ _).mp hL q (by omega))
      ((DerivedCategory.isLE_iff _ _).mp hL (q + 1) (by omega))

/-- The canonical degree-q window maps for a finite subextension of the chosen algebraic closure. -/
theorem proper_unbounded_window_iso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        ↥(pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y)) → (n : ℤ) ≤ d)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) (q : ℤ) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar
          (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj K)) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncLE q).obj K))) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K)))) := by
  have hd' := fun y ↦ dimension_bound _ d (hd y)
  have ht := (indConstructibleDerived_sums_and_truncations
    ℓ E k p₀ hp₀ hpℓ X).2.2.1
  have hA := (ht K q hK).1
  have hW := (ht _ (q - 2 * d - 1) hA).2
  have hB := (ht K (q + 1) hK).2
  have hL := (ht _ (q - 2 * d - 2) hA).1
  have hpK := proper_indConstructible_unbounded
    ℓ E k p₀ hp₀ hpℓ X Y p d hd' K hK
  have hpA := proper_indConstructible_unbounded
    ℓ E k p₀ hp₀ hpℓ X Y p d hd' _ hA
  have hpW := proper_indConstructible_unbounded
    ℓ E k p₀ hp₀ hpℓ X Y p d hd' _ hW
  have hpB := proper_indConstructible_unbounded
    ℓ E k p₀ hp₀ hpℓ X Y p d hd' _ hB
  have hpL := proper_indConstructible_unbounded
    ℓ E k p₀ hp₀ hpℓ X Y p d hd' _ hL
  have hlow := hpB.2.2.1 (q + 1) (by infer_instance)
  have hupp := hpL.2.2.2 (q - 2 * d - 2) (by infer_instance)
  have hupp' :
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
      ((DerivedCategory.TStructure.t.truncLE (q - 2 * d - 2)).obj
        ((DerivedCategory.TStructure.t.truncLE q).obj K))).IsLE (q - 1) := by
    have he : q - 2 * d - 2 + 2 * d + 1 = q - 1 := by omega
    rw [he] at hupp
    exact hupp
  exact ⟨hpK.2.1 q, hpA.2.1 q, hpW.2.1 q,
    window_maps_of_bounds
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor
      K q d hlow hupp'⟩

/-- The canonical degree-q window maps for the condensed algebraic closure. -/
theorem proper_unbounded_window_iso_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        ↥(pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y)) → (n : ℤ) ≤ d)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) (q : ℤ) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj K)) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncLE q).obj K))) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K)))) := by
  have hd' := fun y ↦ dimension_bound _ d (hd y)
  have ht := (indConstructibleDerived_sums_and_truncations_padicAlgCl
    ℓ k p₀ hp₀ hpℓ X).2.2.1
  have hA := (ht K q hK).1
  have hW := (ht _ (q - 2 * d - 1) hA).2
  have hB := (ht K (q + 1) hK).2
  have hL := (ht _ (q - 2 * d - 2) hA).1
  have hpK := proper_indConstructible_unbounded_padicAlgCl
    ℓ k p₀ hp₀ hpℓ X Y p d hd' K hK
  have hpA := proper_indConstructible_unbounded_padicAlgCl
    ℓ k p₀ hp₀ hpℓ X Y p d hd' _ hA
  have hpW := proper_indConstructible_unbounded_padicAlgCl
    ℓ k p₀ hp₀ hpℓ X Y p d hd' _ hW
  have hpB := proper_indConstructible_unbounded_padicAlgCl
    ℓ k p₀ hp₀ hpℓ X Y p d hd' _ hB
  have hpL := proper_indConstructible_unbounded_padicAlgCl
    ℓ k p₀ hp₀ hpℓ X Y p d hd' _ hL
  have hlow := hpB.2.2.1 (q + 1) (by infer_instance)
  have hupp := hpL.2.2.2 (q - 2 * d - 2) (by infer_instance)
  have hupp' :
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
      ((DerivedCategory.TStructure.t.truncLE (q - 2 * d - 2)).obj
        ((DerivedCategory.TStructure.t.truncLE q).obj K))).IsLE (q - 1) := by
    have he : q - 2 * d - 2 + 2 * d + 1 = q - 1 := by omega
    rw [he] at hupp
    exact hupp
  exact ⟨hpK.2.1 q, hpA.2.1 q, hpW.2.1 q,
    window_maps_of_bounds
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor
      K q d hlow hupp'⟩

end AlgebraicGeometry.ProEtale
