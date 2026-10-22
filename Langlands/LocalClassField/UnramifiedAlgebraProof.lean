import Langlands.LocalClassField.UnramifiedAlgebraStatement
import Mathlib.RingTheory.NormTrace
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.Ring

namespace Langlands.LocalClassField.UnramifiedAlgebra

universe u v

open IsLocalRing Module

section Quotients

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

local notation "p" => maximalIdeal R
local notation "q" => Ideal.map (algebraMap R S) p

attribute [local instance] Ideal.Quotient.field

omit [IsLocalRing S] in
private theorem norm_quotient_mk (x : S) :
    Algebra.norm (R ⧸ p) (Ideal.Quotient.mk q x) =
      Ideal.Quotient.mk p (Algebra.norm R x) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (basisQuotient b),
    RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotient_apply, LinearMap.mul_apply', RingHom.mapMatrix_apply, Matrix.map_apply, ← map_mul,
    basisQuotient_repr]

private theorem trace_residue_lift [Finite (ResidueField S)]
    (h : q = maximalIdeal S) (b : R) :
    ∃ a : S, Algebra.trace R S a - b ∈ p := by
  have : Ideal.IsMaximal q := h.symm ▸ inferInstance
  have : Finite (S ⧸ q) := Finite.of_equiv (ResidueField S)
    (Ideal.quotEquivOfEq h).symm.toEquiv
  obtain ⟨a, ha⟩ := Algebra.trace_surjective (R ⧸ p) (S ⧸ q) (Ideal.Quotient.mk p b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨a, (Ideal.Quotient.eq_zero_iff_mem).mp ?_⟩
  rw [map_sub, ← Algebra.trace_quotient_mk, ha, sub_self]

private theorem norm_residue_lift [Finite (ResidueField S)]
    (h : q = maximalIdeal S) (y : Rˣ) :
    ∃ x : Sˣ, (y : R) - Algebra.norm R (x : S) ∈ p := by
  have : Ideal.IsMaximal q := h.symm ▸ inferInstance
  have : Finite (S ⧸ q) := Finite.of_equiv (ResidueField S)
    (Ideal.quotEquivOfEq h).symm.toEquiv
  obtain ⟨z, hz⟩ := FiniteField.unitsMap_norm_surjective (R ⧸ p) (S ⧸ q)
    (Units.map (Ideal.Quotient.mk p) y)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (z : S ⧸ q)
  have hau : IsUnit a := by
    apply (residue_ne_zero_iff_isUnit a).mp
    intro ha0
    have ham : a ∈ maximalIdeal S := (Ideal.Quotient.eq_zero_iff_mem).mp ha0
    have : (z : S ⧸ q) = 0 := by
      rw [← ha]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (h.symm ▸ ham)
    exact z.ne_zero this
  obtain ⟨x, rfl⟩ := hau
  refine ⟨x, (Ideal.Quotient.eq_zero_iff_mem).mp ?_⟩
  have hz' := congrArg (fun t : (R ⧸ p)ˣ => (t : R ⧸ p)) hz
  change Algebra.norm (R ⧸ p) (z : S ⧸ q) = Ideal.Quotient.mk p (y : R) at hz'
  rw [map_sub, ← norm_quotient_mk, ha, hz', sub_self]

end Quotients

section Congruences

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

omit [IsLocalRing R] in
private theorem correction_mem (I : Ideal R) (y v : Rˣ)
    (h : (y : R) - (v : R) ∈ I) :
    ((y * v⁻¹ : Rˣ) : R) - 1 ∈ I := by
  have heq : ((y * v⁻¹ : Rˣ) : R) - 1 =
      ((y : R) - (v : R)) * (v⁻¹ : Rˣ) := by
    simp only [Units.val_mul, sub_mul, Units.mul_inv]
  rw [heq]
  exact I.mul_mem_right _ h

private theorem norm_preserves (π : R)
    (hR : maximalIdeal R = Ideal.span {π})
    (hS : maximalIdeal S = Ideal.span {algebraMap R S π}) :
    NormPreservesUnitCongruences R S := by
  intro n x hx
  rw [hS, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨a, ha⟩ := hx
  have hx' : (x : S) = 1 + (π ^ n) • a := by
    calc
      (x : S) = ((x : S) - 1) + 1 := (sub_add_cancel _ _).symm
      _ = 1 + (π ^ n) • a := by rw [ha]; simp [Algebra.smul_def, map_pow, add_comm]
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (π ^ n) a
  rw [hx', hr, hR, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨Algebra.trace R S a + r * π ^ n, ?_⟩
  ring

private theorem norm_approximates [Finite (ResidueField S)] (π : R)
    (hR : maximalIdeal R = Ideal.span {π})
    (hS : maximalIdeal S = Ideal.span {algebraMap R S π})
    (h : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S) :
    NormApproximatesUnitCongruences R S := by
  intro n y hy
  by_cases hn : n = 0
  · subst n
    obtain ⟨x, hx⟩ := norm_residue_lift h y
    refine ⟨x, by simp, ?_⟩
    simpa using correction_mem (maximalIdeal R) y (Units.map (Algebra.norm R) x) hx
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hπ : π ∈ maximalIdeal R := by rw [hR]; exact Ideal.mem_span_singleton_self _
    have hπn : π ^ n ∈ (maximalIdeal R) ^ n := Ideal.pow_mem_pow hπ n
    rw [hR, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
    obtain ⟨b, hb⟩ := hy
    obtain ⟨a, ha⟩ := trace_residue_lift h b
    have hsa : (π ^ n) • a ∈ (maximalIdeal S) ^ n := by
      rw [hS, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact ⟨a, by simp [Algebra.smul_def, map_pow]⟩
    have hu : IsUnit (1 + (π ^ n) • a) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      have hz : residue S ((π ^ n) • a) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.pow_le_self hn hsa)
      rw [map_add, map_one, hz, add_zero]
      exact one_ne_zero
    obtain ⟨x, hx⟩ := hu
    refine ⟨x, ?_, ?_⟩
    · rw [hx, add_sub_cancel_left]
      exact hsa
    · apply correction_mem ((maximalIdeal R) ^ (n + 1)) y (Units.map (Algebra.norm R) x)
      change (y : R) - Algebra.norm R (x : S) ∈ (maximalIdeal R) ^ (n + 1)
      obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (π ^ n) a
      have hlin : (Algebra.trace R S a - b) * π ^ n ∈ (maximalIdeal R) ^ (n + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mem_mul ha hπn
      have hquad : r * (π ^ n) ^ 2 ∈ (maximalIdeal R) ^ (n + 1) := by
        apply Ideal.mul_mem_left
        apply Ideal.pow_le_pow_right (show n + 1 ≤ n + n by omega)
        simpa [pow_two, pow_add] using Ideal.mul_mem_mul hπn hπn
      have heq : (y : R) - Algebra.norm R (x : S) =
          -((Algebra.trace R S a - b) * π ^ n) - r * (π ^ n) ^ 2 := by
        rw [hx, hr]
        calc
          _ = (((y : R) - 1) - Algebra.trace R S a * π ^ n) - r * (π ^ n) ^ 2 := by ring
          _ = _ := by rw [hb]; ring
      rw [heq]
      exact (maximalIdeal R ^ (n + 1)).sub_mem
        ((maximalIdeal R ^ (n + 1)).neg_mem hlin) hquad

end Congruences

/-- Finite-level norm preservation and approximation for the exact published
finite free unramified local-algebra statement. -/
theorem proof : Statement.{u,v} := by
  intro R S _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hR := hπ.maximalIdeal_eq
  have hS : maximalIdeal S = Ideal.span {algebraMap R S π} := by
    rw [← h, hR, Ideal.map_span, Set.image_singleton]
  exact ⟨norm_preserves π hR hS, norm_approximates π hR hS h⟩

end Langlands.LocalClassField.UnramifiedAlgebra
