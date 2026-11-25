/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoPunctureGlobalSections
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedPrincipalCompletionComparison
import WeilConjectures.RingTheory.CompleteLocalSubideal

/-! # Scalar formal comparison on a complete local puncture

## References

* Stacks Project, Tag 0EII (Lemma 52.12.7), with M = R and a = m
* Tags 0AVY and 0BK0
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Compatible scalar sections on all principal thickenings algebraize uniquely. -/
theorem complete_punctured_principal_formal_sections
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f W n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f W n).appTop
        (s (n + 1)) = s n) →
      ∃! a : Γ(W.toScheme, ⊤), ∀ n,
        (FiniteEtale.Adic.openThickeningMap f W n).appTop a = s n := by
  classical
  dsimp only
  let f := Ideal.Quotient.mk (Ideal.span {g})
  let I := RingHom.ker f
  have hI : I ≤ IsLocalRing.maximalIdeal R := by
    dsimp only [I, f]
    rw [Ideal.mk_ker]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hg)
  have : IsAdicComplete I R := IsAdicComplete.of_le_maximalIdeal R I hI
  let r : CommRingCat.of R ⟶ Γ(W.toScheme, ⊤) :=
    (ΓSpecIso (.of R)).inv ≫ W.ι.appTop
  have hr : Function.Bijective r :=
    (depth_two_puncture_globalSections_bijective R
      (le_trans (by norm_num) hdepth) W hW).comp
        (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).inv)
  let k (n : ℕ) : CommRingCat.of (R ⧸ I ^ (n + 1)) ⟶
      Γ(FiniteEtale.Adic.openThickening f W n, ⊤) :=
    (ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv ≫
      (CategoryTheory.Limits.pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop
  have hrestriction (a : R) (n : ℕ) :
      (FiniteEtale.Adic.openThickeningMap f W n).appTop (r a) =
        k n (Ideal.Quotient.mk (I ^ (n + 1)) a) := by
    have h : r ≫ (FiniteEtale.Adic.openThickeningMap f W n).appTop =
        CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) ≫ k n := by
      dsimp only [r, k, FiniteEtale.Adic.openThickeningMap]
      rw [Category.assoc, ΓSpecIso_inv_naturality_assoc,
        ← Hom.comp_appTop, ← Hom.comp_appTop]
      congr 1
      exact congrArg Hom.appTop (CategoryTheory.Limits.pullback.condition
        (f := W.ι) (g := FiniteEtale.Adic.baseMap f n))
    exact congrArg (fun h ↦ h a) h
  intro s hs
  obtain ⟨q, hq, hu⟩ := punctured_principal_completion_comparison R g hg hdepth W hW s hs
  obtain ⟨b, hb⟩ := AdicCompletion.of_surjective I R q
  have hbq (n : ℕ) : Ideal.Quotient.mk (I ^ (n + 1)) b =
      AdicCompletion.evalₐ I (n + 1) q := by
    rw [← hb, AdicCompletion.evalₐ_of]
  refine ⟨r b, ?_, ?_⟩
  · intro n
    rw [hrestriction, hbq]
    exact hq n
  · intro a ha
    obtain ⟨c, rfl⟩ := hr.2 a
    apply congrArg r
    apply (AdicCompletion.of_injective I R)
    apply (hu _ ?_).trans hb.symm
    intro n
    rw [AdicCompletion.evalₐ_of]
    exact (hrestriction c n).symm.trans (ha n)


end AlgebraicGeometry.Scheme
