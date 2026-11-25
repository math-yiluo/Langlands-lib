/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import Mathlib.RingTheory.Finiteness.Ideal
public import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapKernelLocalTorsion

/-! # CompletedMatchingRingMapKernelTorsion

## References

* Stacks Project, Tags 0BLH, 05ER and 05EU
* Stacks Project, Tag 05ER, localized comparison argument, applied as in 0BLH
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

private theorem ideal_pow_mul_annihilates
    {R P : Type u} [CommRing R] [CommRing P] (φ : R →+* P)
    {I : Ideal R} (hI : I.FG) {t : ℕ} (f : Fin t → R)
    (hf : I = Ideal.span (Set.range f)) (x : P)
    (hx : ∀ i, ∃ e : ℕ, (φ (f i)) ^ e * x = 0) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, φ a * x = 0 := by
  let : Algebra R P := φ.toAlgebra
  have haux : ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
    let J : Ideal R := (Submodule.span R ({x} : Set P)).annihilator
    have hIJ : I ≤ J.radical := by
      rw [hf]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      obtain ⟨e, he⟩ := hx i
      apply (Ideal.mem_radical_iff).2
      refine ⟨e, ?_⟩
      have he' : f i ^ e • x = 0 := by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow]
        exact he
      exact (Submodule.mem_annihilator_span_singleton x _).2 he'
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ hI
    refine ⟨n, ?_⟩
    intro a ha
    exact (Submodule.mem_annihilator_span_singleton x a).1 (hn ha)
  obtain ⟨n, hn⟩ := haux
  refine ⟨n, ?_⟩
  intro a ha
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hn a ha

/-- Kernel elements are maximal-ideal-power torsion. -/
theorem completedRingMap_kernel_torsion
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    ∀ x, D.completedRingMap x = 0 → ∃ n : ℕ,
      ∀ a ∈ IsLocalRing.maximalIdeal A ^ n,
        (D.baseMap ≫ pushout.inl _ _).hom a * x = 0 := by
  intro x hx
  have hfg : (IsLocalRing.maximalIdeal A).FG :=
    Ideal.fg_of_isNoetherianRing _
  obtain ⟨t, f, hf, hlocal⟩ := D.completedRingMap_kernel_local_torsion hU x hx
  exact ideal_pow_mul_annihilates (D.baseMap ≫ pushout.inl _ _).hom hfg f hf x hlocal

end AlgebraicGeometry.Scheme.CompletionGluingData
