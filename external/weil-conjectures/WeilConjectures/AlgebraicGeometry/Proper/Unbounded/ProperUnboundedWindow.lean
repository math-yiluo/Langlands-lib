/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBound
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Proper.ProperIndConstructibleUnbounded
import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedWindowIso

/-!
# Proper direct image of unbounded ind-constructible complexes

The schemes have the standing setting of the uniform bound for proper direct images. All
filtered diagrams are small in the coefficient universe. The window assertion records the two
cohomology arrows of the truncation zigzag. Their composite, the inverse of the first followed
by the second, is the required isomorphism in the full subcategory of ind-constructible
modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma dimensionBound_of_nat_tests (δ : WithBot ℕ∞) (d : ℤ)
    (hδ : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ δ → (n : ℤ) ≤ d) :
    δ ≤ if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥ := by
  by_cases hd : 0 ≤ d
  · rw [ite_eq_left hd]
    by_contra hle
    have hsucc : ((d.toNat + 1 : ℕ) : WithBot ℕ∞) ≤ δ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENat.WithBot.add_one_le_iff).2 (lt_of_not_ge hle)
    have := hδ (d.toNat + 1) hsucc
    omega
  · rw [ite_eq_right hd]
    apply le_of_eq
    by_contra hne
    have hzero : (0 : WithBot ℕ∞) ≤ δ := by
      cases δ with
      | bot => exact False.elim (hne rfl)
      | coe a => exact WithBot.coe_le_coe.mpr (by simp)
    have := hδ 0 hzero
    omega

/-- Derived pushforward along `p` preserves complexes with ind-constructible cohomology, has
amplitude `[0, 2d + 1]`, and in degree `q` its cohomology is computed on the window
`τ^{≥ q - 2d - 1} τ^{≤ q} K`: the images of `truncLEι` and `truncGEπ` are isomorphisms. -/
def ProperUnboundedWindowAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (d : ℤ) : Prop :=
  ∀ K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) →
    (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K))) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K).IsLE (b + 2 * d + 1)) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K).IsGE a) ∧
    (∀ q : ℤ,
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj
            ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
              ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.map
          ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.map
          ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))))

/-- Proper pushforward of unbounded complexes with ind-constructible finite-extension
cohomology preserves that property, has amplitude [0,2d+1], and has the stated finite window. -/
theorem properUnboundedWindow
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperUnboundedWindowAssertions (Profinite.continuousMapRingObj.{u} E) p d := by
  intro K hK
  have hdim := fun y ↦ dimensionBound_of_nat_tests _ d (hd y)
  have h := proper_indConstructible_unbounded ℓ E k p₀ hp₀ hpℓ X Y p d hdim
  have hK' := h K hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hK'.2.1
  · exact hK'.2.2.2
  · exact hK'.2.2.1
  · intro q
    exact (proper_unbounded_window_iso ℓ E k p₀ hp₀ hpℓ X Y p d hd K hK q).2.2

/-- The same unbounded proper-window theorem for the condensed algebraic closure. -/
theorem properUnboundedWindow_padicAlgCl
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
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperUnboundedWindowAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p d := by
  intro K hK
  have hdim := fun y ↦ dimensionBound_of_nat_tests _ d (hd y)
  have h := proper_indConstructible_unbounded_padicAlgCl ℓ k p₀ hp₀ hpℓ X Y p d hdim
  have hK' := h K hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hK'.2.1
  · exact hK'.2.2.2
  · exact hK'.2.2.1
  · intro q
    exact (proper_unbounded_window_iso_padicAlgCl ℓ k p₀ hp₀ hpℓ X Y p d hd K hK q).2.2

end AlgebraicGeometry.ProEtale
