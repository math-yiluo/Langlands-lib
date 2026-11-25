/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedThickeningRestriction
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-!
# Compatible sections of punctured power-series thickenings

## References

* Stacks Project, Tag 0EY9, first displayed inverse-limit calculation
* Stacks Project, Tag 0EY9, first displayed calculation, using depth-two Hartogs (Tag 0BK0)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Compatible sections on the quotient-power thickenings of the punctured zero
section determine a unique power series, by their monomial coefficients. -/
theorem existsUnique_powerSeries_punctured_thickening_sections
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V n, ⊤))
    (hs : ∀ n, (FiniteEtale.Adic.openThickeningTransition
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V n).appTop
        (s (n + 1)) = s n) :
    ∃! b : MvPowerSeries (Fin d) A, ∀ n,
      ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop ≫
        (FiniteEtale.Adic.openThickeningMap
          (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V n).appTop) b = s n :=
  by
  classical
  let B := MvPowerSeries (Fin d) A
  let f := MvPowerSeries.constantCoeff (σ := Fin d) (R := A)
  let I := RingHom.ker f
  have hI : I = Ideal.span (Set.range (MvPowerSeries.X : Fin d → B)) := by
    ext b
    change f b = 0 ↔ _
    have hcoeff := power_series_mem_combined_ideal_pow_iff A (⊥ : Ideal A) d 1 b
    simp only [Ideal.map_bot, bot_sup_eq, pow_one] at hcoeff
    rw [hcoeff]
    constructor
    · intro hb E hE
      have hE0 : E = 0 := (Finsupp.degree_eq_zero_iff E).mp (by omega)
      subst E
      simpa [f, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hb
    · intro hb
      simpa [f, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hb 0 (by simp)
  have : IsAdicComplete I B := by
    rw [hI]
    infer_instance
  let k (n : ℕ) : CommRingCat.of (B ⧸ I ^ (n + 1)) ⟶
      Γ(FiniteEtale.Adic.openThickening f V n, ⊤) :=
    (ΓSpecIso (.of (B ⧸ I ^ (n + 1)))).inv ≫
      (pullback.snd V.ι (FiniteEtale.Adic.baseMap f n)).appTop
  have hkbij (n : ℕ) : Function.Bijective (k n).hom :=
    bijective_powerSeries_punctured_thickening_restriction A hdepth d hd V hV n
  let q (n : ℕ) : B ⧸ I ^ (n + 1) :=
    (Equiv.ofBijective (k n).hom (hkbij n)).symm (s n)
  have hk (n : ℕ) : k n (q n) = s n :=
    (Equiv.ofBijective (k n).hom (hkbij n)).apply_symm_apply (s n)
  have hnatural (n : ℕ) :
      CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 2) ≤ I ^ (n + 1))) ≫
        k n = k (n + 1) ≫ (FiniteEtale.Adic.openThickeningTransition f V n).appTop := by
    dsimp only [k]
    rw [ΓSpecIso_inv_naturality_assoc]
    rw [← Hom.comp_appTop, Category.assoc, ← Hom.comp_appTop]
    congr 1
    simp [FiniteEtale.Adic.openThickeningTransition, FiniteEtale.Adic.baseTransition]
  have hq (n : ℕ) :
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
        (q (n + 1)) = q n := by
    apply (hkbij n).1
    have hn := congrArg (fun g ↦ g.hom (q (n + 1))) (hnatural n)
    change (k n).hom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) (q (n + 1))) =
      (FiniteEtale.Adic.openThickeningTransition f V n).appTop (k (n + 1) (q (n + 1)))
      at hn
    rw [hk] at hn
    exact (hn.trans (hs n)).trans (hk n).symm
  let c (n : ℕ) : B := (q n).out
  have hc (n : ℕ) : Ideal.Quotient.mk (I ^ (n + 1)) (c n) = q n :=
    Ideal.Quotient.mk_out _
  have hadj (n : ℕ) :
      Ideal.Quotient.mk (I ^ (n + 1)) (c (n + 1)) =
        Ideal.Quotient.mk (I ^ (n + 1)) (c n) := by
    rw [hc, ← hq n, ← hc (n + 1), Ideal.Quotient.factor_mk]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      Ideal.Quotient.mk (I ^ (m + 1)) (c m) =
        Ideal.Quotient.mk (I ^ (m + 1)) (c n) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      have h := congrArg
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)))
        (hadj n).symm
      simpa only [Ideal.Quotient.factor_mk] using h
  obtain ⟨b, hb⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I B)
    (f := c) (fun {m n} hmn ↦ by
      have h := congrArg (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ m))) (hcauchy hmn)
      simpa only [Ideal.Quotient.factor_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
        SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] using h)
  have hbq (n : ℕ) : Ideal.Quotient.mk (I ^ (n + 1)) b = q n := by
    have hb' : Ideal.Quotient.mk (I ^ (n + 1)) (c (n + 1)) =
        Ideal.Quotient.mk (I ^ (n + 1)) b := by
      simpa only [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top,
        Ideal.Quotient.mk_eq_mk_iff_sub_mem] using hb (n + 1)
    rw [← hb', hadj n, hc]
  have hrestriction (a : B) (n : ℕ) :
      ((ΓSpecIso (.of B)).inv ≫ V.ι.appTop ≫
        (FiniteEtale.Adic.openThickeningMap f V n).appTop) a =
      k n (Ideal.Quotient.mk (I ^ (n + 1)) a) := by
    change (((ΓSpecIso (.of B)).inv ≫ V.ι.appTop ≫
      (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)).appTop) a) = _
    have h : (ΓSpecIso (.of B)).inv ≫ V.ι.appTop ≫
        (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)).appTop =
        CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) ≫ k n := by
      dsimp only [k]
      rw [ΓSpecIso_inv_naturality_assoc, ← Hom.comp_appTop, ← Hom.comp_appTop]
      congr 1
      exact congrArg Hom.appTop (pullback.condition
        (f := V.ι) (g := FiniteEtale.Adic.baseMap f n))
    exact congrArg (fun g ↦ g a) h
  refine ⟨b, ?_, ?_⟩
  · intro n
    rw [hrestriction, hbq, hk]
  · intro a ha
    apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
    intro n
    have han : Ideal.Quotient.mk (I ^ (n + 1)) a = q n := by
      apply (hkbij n).1
      rw [← hrestriction, ha, hk]
    have heq := han.trans (hbq n).symm
    have h := congrArg
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))) heq
    simpa only [Ideal.Quotient.factor_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] using h

end AlgebraicGeometry.Scheme
