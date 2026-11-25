/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedWindow
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedCoproductComparison
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTruncationCoproducts
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedSums
import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedWindowBounded
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts

/-!
# Proper direct image preserves arbitrary small direct sums

The standing setting is that of the proper window and heart-bound lemmas: separated
finite-type schemes over k, with positive characteristic different from ell, and morphisms
over k.

## Implementation details

Coproducts are given by colimit cofans, including their existence. The comparison is
induced by the images of the source coprojections. Membership of both coproducts in the
full subcategory of complexes with ind-constructible cohomology makes this precisely the
comparison in that subcategory. No choice of an ambient coproduct or additional
coproduct-existence hypothesis is imposed on callers.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Total derived pushforward along `p` preserves complexes with ind-constructible cohomology
(ind-objects of constant-model constructible modules), and the canonical comparison map from
the coproduct of the pushforwards to the pushforward of a coproduct is invertible. -/
def ProperUnboundedCoproductAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  (∀ K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) →
    ∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K))) ∧
  (∀ (I : Type (u + 1))
      (K : I → DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
    (∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
    ∃ (c : Cofan K) (_ : IsColimit c)
      (c' : Cofan (fun i ↦ (CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj (K i)))
      (hc' : IsColimit c'),
      (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj c.pt)) ∧
      (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj c'.pt)) ∧
      IsIso (hc'.desc (Cofan.mk
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj c.pt)
        (fun i ↦ (CondensedRing.lowerStar Λ p).rightDerivedFunctor.map (c.inj i)))))

/-- Proper direct image preserves arbitrary small sums of unbounded ind-constructible
complexes in the standing scheme setting, with finite-extension condensed coefficients
and a uniform geometric-fibre bound. -/
theorem properUnbounded_preservesCoproducts
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞)) :
    ProperUnboundedCoproductAssertions (Profinite.continuousMapRingObj.{u} E) p := by
  have hdim : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ (d : ℤ) := by
    intro y n hn
    have hnd : (n : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := hn.trans (hd y)
    exact_mod_cast hnd
  have hw := properUnboundedWindow ℓ E k p₀ hp₀ hpℓ X Y p d hdim
  refine ⟨?_, ?_⟩
  · intro K hK n
    exact (hw K hK).1 n
  · have sx := indConstructibleDerived_sums_and_truncations ℓ E k p₀ hp₀ hpℓ X
    have sy := indConstructibleDerived_sums_and_truncations ℓ E k p₀ hp₀ hpℓ Y
    apply properUnbounded_coproductComparison (Profinite.continuousMapRingObj E) p d hw
      sx.2.1 sy.2.1 sx.2.2.1
    · intro I D c hc q
      let B := pulledBackModuleObjects (Profinite.continuousMapRingObj E) Y
      let : HasColimitsOfShape (Discrete I) B :=
        IsGrothendieckAbelian.hasColimitsOfShape_discrete B I
      let : HasExactColimitsOfShape (Discrete I) B :=
        IsGrothendieckAbelian.hasExactColimitsOfShape_discrete B I
      exact ⟨isColimitOfPreserves (DerivedCategory.homologyFunctor B q) hc⟩
    · intro I K c hc q r
      have := derivedTruncation_preservesCoproducts (Profinite.continuousMapRingObj E) X I q r
      exact ⟨isColimitOfPreserves _ hc⟩
    · intro a b I M hM hb
      obtain ⟨c, hc, c', hc', hi⟩ := properUnboundedWindowBounded ℓ E p a b I M hM hb
      refine ⟨c, hc, ?_⟩
      have := hi
      exact ⟨(Cofan.isColimitMapCoconeEquiv _ M c).2 hc'.ofPointIso⟩

/-- The arbitrary-sum theorem for the condensed algebraic closure, whose sections have
values in a finite subextension, in the standing scheme setting with the same fibre bound. -/
theorem properUnbounded_preservesCoproducts_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞)) :
    ProperUnboundedCoproductAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p := by
  have hdim : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ (d : ℤ) := by
    intro y n hn
    have hnd : (n : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := hn.trans (hd y)
    exact_mod_cast hnd
  have hw := properUnboundedWindow_padicAlgCl ℓ k p₀ hp₀ hpℓ X Y p d hdim
  refine ⟨?_, ?_⟩
  · intro K hK n
    exact (hw K hK).1 n
  · have sx := indConstructibleDerived_sums_and_truncations_padicAlgCl ℓ k p₀ hp₀ hpℓ X
    have sy := indConstructibleDerived_sums_and_truncations_padicAlgCl ℓ k p₀ hp₀ hpℓ Y
    apply properUnbounded_coproductComparison (Profinite.padicAlgClRingObj ℓ) p d hw
      sx.2.1 sy.2.1 sx.2.2.1
    · intro I D c hc q
      let B := pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) Y
      let : HasColimitsOfShape (Discrete I) B :=
        IsGrothendieckAbelian.hasColimitsOfShape_discrete B I
      let : HasExactColimitsOfShape (Discrete I) B :=
        IsGrothendieckAbelian.hasExactColimitsOfShape_discrete B I
      exact ⟨isColimitOfPreserves (DerivedCategory.homologyFunctor B q) hc⟩
    · intro I K c hc q r
      have := derivedTruncation_preservesCoproducts (Profinite.padicAlgClRingObj ℓ) X I q r
      exact ⟨isColimitOfPreserves _ hc⟩
    · intro a b I M hM hb
      obtain ⟨c, hc, c', hc', hi⟩ := properUnboundedWindowBounded_padicAlgCl ℓ p a b I M hM hb
      refine ⟨c, hc, ?_⟩
      have := hi
      exact ⟨(Cofan.isColimitMapCoconeEquiv _ M c).2 hc'.ofPointIso⟩

end AlgebraicGeometry.ProEtale
