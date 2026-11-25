/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedPrincipalFiniteLevelLift
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedPrincipalRestrictionKernel

/-! # Formal sections as an element of the principal adic completion

## References

* Stacks Project, Tag 0BLD (Lemma 52.3.2, p = 0), as used in Tag 0EII
* Tags 0AVY and 0BK0
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private noncomputable abbrev scalarRestriction {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (W : (Spec (.of R)).Opens) (n : ℕ) :
    R →+* Γ(FiniteEtale.Adic.openThickening f W n, ⊤) :=
  ((ΓSpecIso (.of R)).inv ≫
    (FiniteEtale.Adic.openThickeningMap f W n ≫ W.ι).appTop).hom

private theorem scalarRestriction_transition {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (W : (Spec (.of R)).Opens) (n : ℕ) (a : R) :
    (FiniteEtale.Adic.openThickeningTransition f W n).appTop
      (scalarRestriction f W (n + 1) a) = scalarRestriction f W n a := by
  change (((ΓSpecIso (.of R)).inv ≫
    (FiniteEtale.Adic.openThickeningMap f W (n + 1) ≫ W.ι).appTop) ≫
      (FiniteEtale.Adic.openThickeningTransition f W n).appTop) a = _
  rw [Category.assoc, ← Scheme.Hom.comp_appTop]
  congr 2
  simp [FiniteEtale.Adic.openThickeningTransition, FiniteEtale.Adic.openThickeningMap]

private theorem scalarRestriction_quotient {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (W : (Spec (.of R)).Opens) (n : ℕ) (a : R) :
    ((ΓSpecIso (.of (R ⧸ (RingHom.ker f) ^ (n + 1)))).inv ≫
      (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop)
        (Ideal.Quotient.mk ((RingHom.ker f) ^ (n + 1)) a) =
      scalarRestriction f W n a := by
  change (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker f) ^ (n + 1))) ≫
    (ΓSpecIso (.of (R ⧸ (RingHom.ker f) ^ (n + 1)))).inv ≫
      (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop) a = _
  rw [← Category.assoc, ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Hom.comp_appTop]
  change ((ΓSpecIso (.of R)).inv ≫
    (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n) ≫
      FiniteEtale.Adic.baseMap f n).appTop) a = _
  rw [← pullback.condition]

/-- On a depth-three puncture, formal sections determine an element of the
principal adic completion, even when the local ring is not complete. -/
theorem punctured_principal_completion_comparison
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    let I := RingHom.ker f
    ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f W n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f W n).appTop
        (s (n + 1)) = s n) →
      ∃! q : AdicCompletion I R, ∀ n,
        ((ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv ≫
          (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop)
            (AdicCompletion.evalₐ I (n + 1) q) = s n := by
  classical
  dsimp only
  let f := Ideal.Quotient.mk (Ideal.span {g})
  let I := RingHom.ker f
  intro s hs
  choose b hb using punctured_principal_finite_level_lift R g hg hdepth W hW s hs
  choose k hk hker using punctured_principal_restriction_kernel R g hg hdepth W hW
  change ∀ n, scalarRestriction f W n (b n) = s n at hb
  change ∀ n a b, scalarRestriction f W (k n) a = scalarRestriction f W (k n) b →
    a - b ∈ I ^ (n + 1) at hker
  have hdown (n m : ℕ) (hnm : n ≤ m) (a : R)
      (ha : scalarRestriction f W m a = s m) : scalarRestriction f W n a = s n := by
    induction m, hnm using Nat.le_induction with
    | base => exact ha
    | succ m hnm ih =>
      apply ih
      rw [← scalarRestriction_transition f W m a, ha, hs]
  let a : ℕ → R := fun n ↦ b (k n)
  have ha (n : ℕ) : scalarRestriction f W n (a n) = s n :=
    hdown n (k n) (hk n) _ (hb (k n))
  have hcoh (n m : ℕ) (hnm : n ≤ m) :
      Ideal.Quotient.mk (I ^ (n + 1)) (a n) =
        Ideal.Quotient.mk (I ^ (n + 1)) (a m) := by
    let j := max (k n) (k m)
    have hn : a n - b j ∈ I ^ (n + 1) := by
      apply hker n
      exact (hb (k n)).trans
        (hdown (k n) j (Nat.le_max_left _ _) _ (hb j)).symm
    have hm : a m - b j ∈ I ^ (m + 1) := by
      apply hker m
      exact (hb (k m)).trans
        (hdown (k m) j (Nat.le_max_right _ _) _ (hb j)).symm
    have hm' := (Ideal.pow_le_pow_right (Nat.succ_le_succ hnm) :
      I ^ (m + 1) ≤ I ^ (n + 1)) hm
    exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hn).trans
      ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hm').symm
  let A : AdicCompletion.AdicCauchySequence I R :=
    AdicCompletion.AdicCauchySequence.mk I R a (fun n ↦ by
      apply SModEq.sub_mem.mpr
      have h := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
        (hcoh n (n + 1) (Nat.le_succ n))
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
        (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n) h)
  let q := AdicCompletion.mk I R A
  have hq (n : ℕ) :
      ((ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv ≫
        (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop)
          (AdicCompletion.evalₐ I (n + 1) q) = s n := by
    rw [AdicCompletion.evalₐ_mk]
    rw [scalarRestriction_quotient]
    exact hdown n (n + 1) (Nat.le_succ n) _ (ha (n + 1))
  refine ⟨q, hq, ?_⟩
  intro r hr
  obtain ⟨B, rfl⟩ := AdicCompletion.mk_surjective I R r
  apply AdicCompletion.ext_evalₐ
  intro n
  cases n with
  | zero =>
    have : Subsingleton (R ⧸ I ^ 0) := by
      simp only [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    have hB : scalarRestriction f W (k n) (B (k n + 1)) = s (k n) := by
      have h := hr (k n)
      change ((ΓSpecIso (.of (R ⧸ I ^ (k n + 1)))).inv ≫
        (pullback.snd W.ι (FiniteEtale.Adic.baseMap f (k n))).appTop)
          (AdicCompletion.evalₐ I (k n + 1) (AdicCompletion.mk I R B)) = s (k n) at h
      rw [AdicCompletion.evalₐ_mk, scalarRestriction_quotient] at h
      exact h
    have hmem : B (k n + 1) - a n ∈ I ^ (n + 1) := by
      apply hker n
      exact hB.trans (hb (k n)).symm
    have hBc : Ideal.Quotient.mk (I ^ (n + 1)) (B (n + 1)) =
        Ideal.Quotient.mk (I ^ (n + 1)) (B (k n + 1)) := by
      have h := B.property (Nat.succ_le_succ (hk n))
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp h
    exact hBc.trans (((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hmem).trans
      (hcoh n (n + 1) (Nat.le_succ n)))

end AlgebraicGeometry.Scheme
