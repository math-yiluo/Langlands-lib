/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import WeilConjectures.Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Valuations of Kummer elements fixed by inertia

Let `R` be a Dedekind domain with fraction field `K`, `Ω` a Galois extension of `K`, `m` a maximal
ideal of `R` with perfect residue field and `Q` a maximal ideal over `m` of the integral closure of
`R` in `Ω`. If an `N`-th root `x ∈ Ω` of `f ∈ K` is fixed by the inertia group of `Q`, then the
`m`-adic valuation of `f` is an `N`-th power
(`Ideal.exists_valuation_eq_exp_mul_of_forall_inertia`): the extension `K(x) / K` is unramified at
the prime of the integral closure of `R` in `K(x)` below `Q`
(`Ideal.ramificationIdx_comap_integralClosureMap_eq_one`), so that the `m`-adic valuation of `f`
is the valuation of `x ^ N` at that prime.
-/

@[expose] public section

open IntermediateField IsDedekindDomain

namespace Ideal

variable {R K Ω : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω]

-- the elaboration of the integral closure instances is slow
/-- **Kummer elements fixed by inertia have unramified valuation.** Let `x ∈ Ω` be nonzero with
`x ^ N = f ∈ K`, fixed by the inertia group of a maximal ideal `Q` of the integral closure of `R`
in `Ω` over a maximal ideal `m ≠ 0` of `R` with perfect residue field. Then the `m`-adic valuation
of `f` is `exp (N b)` for some integer `b`. -/
theorem exists_valuation_eq_exp_mul_of_forall_inertia (m : Ideal R) [m.IsMaximal]
    [PerfectField m.ResidueField] (hm : m ≠ ⊥) (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal]
    [Q.LiesOver m] {N : ℕ} {x : Ω} (hx : x ≠ 0) {f : K} (hf : algebraMap K Ω f = x ^ N)
    (hI : ∀ σ ∈ Q.inertia Gal(Ω/K), σ x = x) :
    ∃ b : ℤ, (⟨m, inferInstance, hm⟩ : HeightOneSpectrum R).valuation K f =
      WithZero.exp ((N : ℤ) * b) := by
  have hRΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  -- the field `L = K(x)` and the integral closure `T` of `R` in it
  let L : IntermediateField K Ω := K⟮x⟯
  have : FiniteDimensional K L :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) x)
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  let T := integralClosure R L
  have : IsDedekindDomain T := IsIntegralClosure.isDedekindDomain R K L T
  have : Module.Finite R T := IsIntegralClosure.finite R K L T
  have : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R K L T
  let ψ : T →ₐ[R] Ω := (L.val.restrictScalars R).comp (IsScalarTower.toAlgHom R T L)
  have hRT : Function.Injective (algebraMap R T) := fun a b h ↦ hRΩ (by
    have := congrArg ψ h
    rwa [ψ.commutes, ψ.commutes] at this)
  have : Module.IsTorsionFree R T :=
    Module.isTorsionFree_iff_faithfulSMul.2 ((faithfulSMul_iff_algebraMap_injective R T).2 hRT)
  -- inertia fixes `L = K(x)`, hence the image of `T`
  have hI' : ∀ σ ∈ Q.inertia Gal(Ω/K), ∀ y : T, σ (ψ y) = ψ y := by
    intro σ hσ y
    have hle : L ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      rintro _ ⟨n, rfl⟩
      exact (MulAction.stabilizer Gal(Ω/K) x).zpow_mem (hI σ hσ) n
    exact (IntermediateField.mem_fixedField_iff _ _).1 (hle (y : L).2) σ
      (Subgroup.mem_zpowers σ)
  set 𝔭 := Q.comap (integralClosureMap ψ)
  have he := ramificationIdx_comap_integralClosureMap_eq_one ψ Q m hI'
  have hcomp : (integralClosureMap ψ).comp (algebraMap R T) =
      algebraMap R (integralClosure R Ω) := by
    ext r
    exact ψ.commutes r
  have : 𝔭.LiesOver m := ⟨by
    rw [Ideal.under, Ideal.comap_comap, hcomp]
    exact Ideal.over_def Q m⟩
  have h𝔭 : 𝔭 ≠ ⊥ := fun h ↦ hm (by
    rw [Ideal.over_def 𝔭 m, h, Ideal.under, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hRT)
  let v : HeightOneSpectrum R := ⟨m, inferInstance, hm⟩
  let w : HeightOneSpectrum T := ⟨𝔭, inferInstance, h𝔭⟩
  have : w.asIdeal.LiesOver v.asIdeal := inferInstanceAs (𝔭.LiesOver m)
  have hval := HeightOneSpectrum.valuation_liesOver (K := K) L v w f
  rw [show w.asIdeal.ramificationIdx R = 1 from he, pow_one] at hval
  have hxL : algebraMap K L f = ⟨x, mem_adjoin_simple_self K x⟩ ^ N :=
    Subtype.ext (by simpa using hf)
  rw [hxL, map_pow] at hval
  have hw0 : w.valuation L ⟨x, mem_adjoin_simple_self K x⟩ ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact fun h ↦ hx (congrArg Subtype.val h)
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.1 hw0
  refine ⟨Multiplicative.toAdd b, ?_⟩
  rw [hval, ← hb, WithZero.exp, ← WithZero.coe_pow]
  congr 1

end Ideal
