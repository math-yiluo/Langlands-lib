/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables

/-! # Flatness of truncated power-series algebras

## References

* Stacks Project, Tag 0EY9, finite monomial calculation
* Stacks Project, Tag 0EY9, first displayed calculation at a finite index
-/

@[expose] public section

universe u
namespace MvPowerSeries

/-- The constants map to a finite total-degree truncation is flat. -/
theorem truncated_constants_flat (A : Type u) [CommRing A] (d n : ℕ) :
    ((Ideal.Quotient.mk
      ((RingHom.ker (constantCoeff (σ := Fin d) (R := A))) ^ (n + 1))).comp
        (C (σ := Fin d) (R := A))).Flat := by
  classical
  let B := MvPowerSeries (Fin d) A
  let I : Ideal B := (RingHom.ker (constantCoeff (σ := Fin d) (R := A))) ^ (n + 1)
  let Q := B ⧸ I
  let E := {e : Fin d →₀ ℕ // e.degree < n + 1}
  let : Fintype E := (Finsupp.finite_of_degree_lt (n + 1)).fintype
  have hmem (F : B) : F ∈ I ↔ ∀ e : E, coeff e.1 F = 0 := by
    have hk := (quotient_first_variables_kernels A d 0 (Nat.zero_le d)).2
    dsimp [I]
    rw [hk]
    have h := power_series_mem_combined_ideal_pow_iff A (⊥ : Ideal A) d (n + 1) F
    simp only [Ideal.map_bot, bot_sup_eq] at h
    rw [h]
    constructor
    · intro h e
      have he := h e.1 e.2
      simpa [Ideal.bot_pow (Nat.sub_ne_zero_of_lt e.2)] using he
    · intro h e he
      simp [h ⟨e, he⟩]
  let low : (E → A) →ₗ[A] B :=
    { toFun := fun v ↦ ∑ e : E, monomial e.1 (v e)
      map_add' := by
        intro v w
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply] }
  have hcoeff (v : E → A) (e : E) : coeff e.1 (low v) = v e := by
    change coeff e.1 (∑ a : E, monomial a.1 (v a)) = v e
    rw [map_sum]
    rw [Finset.sum_eq_single e]
    · exact coeff_monomial_same e.1 (v e)
    · intro a _ hne
      apply coeff_monomial_ne
      intro h
      exact hne (Subtype.ext h.symm)
    · simp
  let l : (E → A) →ₗ[A] Q := (Ideal.Quotient.mkₐ A I).toLinearMap.comp low
  have hl : Function.Bijective l := by
    constructor
    · intro v w hvw
      have hdiff : low v - low w ∈ I :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hvw
      have hc := (hmem _).mp hdiff
      funext e
      have he := hc e
      rw [map_sub, hcoeff, hcoeff, sub_eq_zero] at he
      exact he
    · intro q
      obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective q
      refine ⟨(fun e ↦ coeff e.1 F), ?_⟩
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      apply (hmem _).mpr
      intro e
      rw [map_sub, hcoeff, sub_self]
  let e : (E → A) ≃ₗ[A] Q := LinearEquiv.ofBijective l hl
  have hflat : Module.Flat A Q := Module.Flat.of_linearEquiv e.symm
  change (algebraMap A Q).Flat
  exact RingHom.flat_algebraMap_iff.mpr hflat

end MvPowerSeries
