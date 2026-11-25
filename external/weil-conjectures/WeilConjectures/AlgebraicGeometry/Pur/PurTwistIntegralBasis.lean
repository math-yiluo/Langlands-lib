/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-! # A finite integral coefficient basis
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace AlgebraicGeometry.Scheme

/-- The chosen valuation ring has a finite basis over the p-adic integers, for
precisely the canonical inclusion used in the Tate-twist construction. -/
theorem purTwistIntegralBasis (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ k : ℕ, Nonempty (@Module.Basis (Fin k) ℤ_[l]
        (Padic.coefficientExtensionIntegers l E) _ _
        (Module.compHom (Padic.coefficientExtensionIntegers l E) (purTwistIntegersMap l E))) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  let : Algebra ℤ_[l] O := (purTwistIntegersMap l E).toAlgebra
  let : Algebra ℤ_[l] E := ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  have hmap (z : ℤ_[l]) : (purTwistIntegersMap l E z : E) =
      algebraMap ℚ_[l] E (z : ℚ_[l]) :=
    (purTwistIntegersMap_existsUnique l E).exists.choose_spec z
  let : IsScalarTower ℤ_[l] O E := IsScalarTower.of_algebraMap_eq fun z ↦ (hmap z).symm
  have hO := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsFractionRing O E := hO.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing O := hO.2.2.2.2.2.2.2.2.1
  have : IsIntegrallyClosedIn O E :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn E).mp inferInstance
  have hInt (x : E) : x ∈ O ↔ _root_.IsIntegral ℤ_[l] x := by
    constructor
    · intro hx
      have hmon := minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) x)
      have hcoeff := (spectralValue_le_one_iff hmon).mp ((hO.1 x).mp hx)
      have hlift : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨(minpoly ℚ_[l] x).coeff n, hcoeff n⟩, rfl⟩
      obtain ⟨q, hq, _, hqmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
      refine ⟨q, hqmon, ?_⟩
      change q.eval₂ ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])) x = 0
      rw [← Polynomial.eval₂_map, hq]
      exact minpoly.aeval ℚ_[l] x
    · intro hx
      have hx' : _root_.IsIntegral O x := hx.tower_top
      obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := O) (R := O)).mp hx'
      exact hy ▸ y.property
  let : IsIntegralClosure O ℤ_[l] E :=
    ⟨Subtype.val_injective, fun {x} ↦ by
      rw [← hInt]
      exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩⟩
  have : IsScalarTower ℤ_[l] ℚ_[l] E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite ℤ_[l] O := IsIntegralClosure.finite ℤ_[l] ℚ_[l] E O
  have : Module.IsTorsionFree ℤ_[l] E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap ℚ_[l] E).injective.comp
        (show Function.Injective (algebraMap ℤ_[l] ℚ_[l]) from Subtype.val_injective))
  have : Module.Free ℤ_[l] O := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] E O
  exact ⟨Module.finrank ℤ_[l] O, ⟨Module.finBasis ℤ_[l] O⟩⟩

end AlgebraicGeometry.Scheme
