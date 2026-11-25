import Langlands.GaloisCohomology.Field.KummerSequence
import Langlands.Galois.RestrictedRamification.MaximalExtension
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# `S`-units as Galois modules, and their invariants

For a number field `F`, a set `S` of finite places of `F` and an extension `E` of `F`, the
`S`-units of `E` are the units `x` such that `x` and `x⁻¹` are integral over the `S`-integers of
`F` (`sUnitsOf`); for a number field `L` over `F` they are Mathlib's `Set.unit` for the places of
`L` above `S` (`mem_sUnitsOf_iff_mem_unit`). They form a smooth `Gal(E / F)`-module
(`sUnitsModule`), and for `E / F` Galois its invariants are the `S`-units of `F`
(`sUnitsInvariantsEquiv`, `cohomologyZeroSUnitsEquiv`: `H⁰(Gal(E/F), 𝒪_{E,S}ˣ) = 𝒪_{F,S}ˣ`). The
`G_S`-module of `S`-units of `K_S` is `maximalSUnitsModule`.

If `n` is invertible outside `S`, the `n`-th roots of `S`-units of `K_S` lie in `K_S`
(`mem_maximalUnramifiedOutside_of_pow_eq`), by Kummer theory: adjoining an `n`-th root of `a` is
unramified at the places prime to `n` at which `n` divides the valuation of `a`
(`isUnramifiedAt_of_pow_eq`). Hence every `S`-unit of `K_S` is an `n`-th power of an `S`-unit of
`K_S` when `Ω` is separably closed (`exists_pow_eq_of_mem_maximalSUnits`).
-/

namespace Langlands.GaloisCohomology

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory Polynomial
open Langlands.Galois Langlands.ProfiniteCohomology
open scoped NumberField nonZeroDivisors

universe u

noncomputable section

section Valuation

/-- An element integral over a ring whose image has valuation `≤ 1` has valuation `≤ 1`. -/
theorem valuation_le_one_of_isIntegral {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (w : Valuation L (WithZero (Multiplicative ℤ))) (hR : ∀ r : R, w (algebraMap R L r) ≤ 1)
    {x : L} (hx : IsIntegral R x) : w x ≤ 1 := by
  let f : R →+* w.integer := (algebraMap R L).codRestrict w.integer hR
  have hx' : IsIntegral w.integer (RingHom.id L x) :=
    IsIntegral.map_of_comp_eq f (RingHom.id L) (by ext r; rfl) hx
  exact (Valuation.integer.integers w).mem_of_integral hx'

/-- For `0 < a < 1` and `b ≠ 0` in `ℤᵐ⁰`, some power of `a` brings `b` below `1`. -/
theorem exists_mul_pow_le_one {a b : WithZero (Multiplicative ℤ)} (ha0 : a ≠ 0) (ha : a < 1)
    (hb : b ≠ 0) : ∃ N : ℕ, b * a ^ N ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = WithZero.exp k := ⟨_, (WithZero.exp_log ha0).symm⟩
  obtain ⟨m, rfl⟩ : ∃ m, b = WithZero.exp m := ⟨_, (WithZero.exp_log hb).symm⟩
  have hk : k < 0 := by
    rw [← WithZero.exp_zero] at ha
    exact WithZero.exp_lt_exp.1 ha
  refine ⟨m.toNat, ?_⟩
  rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  have : (m.toNat : ℤ) * k ≤ -(m.toNat : ℤ) := by nlinarith [Int.self_le_toNat m]
  rw [nsmul_eq_mul]
  omega

end Valuation

section PlaceUnit

variable {K : Type*} [Field K] [NumberField K]

/-- The `h_K`-th power of a prime of `𝓞 K` is principal, `h_K` the class number. -/
theorem exists_pow_classNumber_eq_span (v : HeightOneSpectrum (𝓞 K)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ v.asIdeal ^ classNumber K = Ideal.span {a} := by
  let I : (Ideal (𝓞 K))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have h1 : ClassGroup.mk0 (I ^ classNumber K) = 1 := by
    rw [map_pow, classNumber, Fintype.card_eq_nat_card]
    exact pow_card_eq_one'
  have h2 := (ClassGroup.mk0_eq_one_iff (I ^ classNumber K).2).mp h1
  obtain ⟨a, ha⟩ := h2.principal
  have ha' : v.asIdeal ^ classNumber K = Ideal.span {a} := by
    rw [SubmonoidClass.coe_pow] at ha
    exact ha
  refine ⟨a, ?_, ha'⟩
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.mpr rfl] at ha'
  exact pow_ne_zero _ v.ne_bot ha'

open scoped Classical in
/-- The valuations of a generator of `vⁿ`: `-n` at `v`, `0` elsewhere. -/
theorem intValuation_of_pow_eq_span {v w : HeightOneSpectrum (𝓞 K)} {a : 𝓞 K} (ha : a ≠ 0)
    {n : ℕ} (h : v.asIdeal ^ n = Ideal.span {a}) :
    w.intValuation a = if w = v then WithZero.exp (-(n : ℤ)) else 1 := by
  rw [intValuation_eq_exp_neg_multiplicity w ha, ← h]
  split_ifs with hw
  · subst hw
    rw [multiplicity_pow_self_of_prime w.prime n]
  · have h0 : multiplicity w.asIdeal (v.asIdeal ^ n) = 0 := by
      refine multiplicity_eq_zero_of_not_dvd fun hdvd => ?_
      apply hw
      have hle : v.asIdeal ≤ w.asIdeal := Ideal.le_of_dvd (w.prime.dvd_of_dvd_pow hdvd)
      exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm
    rw [h0]
    simp

/-- A generator of the principal ideal `v^{h_K}`, as a unit of `K`. -/
def placeUnit (v : HeightOneSpectrum (𝓞 K)) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K (exists_pow_classNumber_eq_span v).choose) <| by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
    exact (exists_pow_classNumber_eq_span v).choose_spec.1

open scoped Classical in
/-- `placeUnit v` has valuation `-h_K` at `v` and `0` at every other finite place. -/
theorem valuationOfNeZero_placeUnit (v w : HeightOneSpectrum (𝓞 K)) :
    w.valuationOfNeZero (placeUnit v) =
      if w = v then Multiplicative.ofAdd (-(classNumber K : ℤ)) else 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, placeUnit, Units.val_mk0,
    valuation_of_algebraMap, intValuation_of_pow_eq_span
      (exists_pow_classNumber_eq_span v).choose_spec.1
      (exists_pow_classNumber_eq_span v).choose_spec.2]
  split_ifs <;> rfl

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- For `v ∈ S`, `placeUnit v` is an `S`-unit. -/
theorem placeUnit_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : placeUnit v ∈ S.unit K := by
  intro w hw
  have hwv : w ≠ v := fun h => hw (h ▸ hv)
  rw [← valuationOfNeZero_eq, valuationOfNeZero_placeUnit]
  simp [hwv]

end PlaceUnit

section KummerRamification

variable {K : Type*} [Field K] [NumberField K]

/-- If `n` divides the valuation of `a` at `v`, then `a cⁿ` is a `v`-adic unit in `𝓞 K` for some `c`. -/
theorem exists_mul_pow_integral_notMem (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0)
    (a : Kˣ) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    ∃ c : K, c ≠ 0 ∧ ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = a * c ^ n ∧ b ∉ v.asIdeal := by
  obtain ⟨m, hm⟩ := hav
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have ha0 : v.valuation K (a : K) ≠ 0 := by simp
  set a' : K := a * (π ^ m) ^ n with ha'
  have hva' : v.valuation K a' = 1 := by
    rw [ha', map_mul, map_pow, map_zpow₀, hπ, ← WithZero.exp_log ha0, hm]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    simp
  obtain ⟨r, d, hrd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := v) a' hva'.le
  have hd : (d : 𝓞 K) ∉ v.asIdeal := d.prop
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
    intro h
    apply hd
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp h]
    exact zero_mem _
  refine ⟨π ^ m * algebraMap (𝓞 K) K d, mul_ne_zero (zpow_ne_zero _ hπ0) hdK,
    r * d ^ (n - 1), ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, map_mul, map_pow, ← hrd, ha']
    ring
  · rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) v]
    have h1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) v).mpr hd
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, map_mul, map_pow, ← hrd, map_mul, map_mul, map_pow, hva', h1]
    simp

variable {M : Type*} [Field M] [NumberField M] [Algebra K M]

/-- Kummer theory and ramification: if `M = K(α)` with `αⁿ = a`, `n` prime to `v` and `n` dividing the valuation of `a` at `v`, every prime of `M` above `v` is unramified. -/
theorem isUnramifiedAt_of_pow_eq {n : ℕ} (a : Kˣ) {α : M} (hα : α ^ n = algebraMap K M a)
    (hgen : IntermediateField.adjoin K {α} = ⊤) (v : HeightOneSpectrum (𝓞 K))
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hnv (by simp)
  obtain ⟨c, hc, b, hb, hbv⟩ := exists_mul_pow_integral_notMem v hn a hav
  set x : M := algebraMap K M c * α with hx
  have hxn : x ^ n = algebraMap K M (algebraMap (𝓞 K) K b) := by
    rw [hx, mul_pow, hα, hb, map_mul, map_pow]
    ring
  have hxint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hxn]
    exact b.isIntegral_coe.algebraMap
  let y : 𝓞 M := ⟨x, hxint⟩
  have hyx : algebraMap (𝓞 M) M y = x := rfl
  have hyb : y ^ n = algebraMap (𝓞 K) (𝓞 M) b := by
    apply FaithfulSMul.algebraMap_injective (𝓞 M) M
    rw [map_pow, hyx, hxn, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M]
  have hKx : IntermediateField.adjoin K {x} = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
    have : α = algebraMap K M c⁻¹ * x := by
      rw [hx, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self K x)
  have hgen' : Algebra.adjoin K {algebraMap (𝓞 M) M y} = ⊤ := by
    rw [hyx, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic x), hKx, IntermediateField.top_toSubalgebra]
  have hyint : IsIntegral (𝓞 K) y := Algebra.IsIntegral.isIntegral y
  obtain ⟨g, hg⟩ : minpoly (𝓞 K) y ∣ X ^ n - C b :=
    minpoly.isIntegrallyClosed_dvd hyint (by simp [hyb])
  have hder : aeval y (derivative (minpoly (𝓞 K) y)) * aeval y g = (n : 𝓞 M) * y ^ (n - 1) := by
    have := congrArg (fun p => aeval y (derivative p)) hg
    simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add,
      map_mul, minpoly.aeval, zero_mul, add_zero] at this
    rw [← this]
    simp
  have hnP : (n : 𝓞 M) ∉ P := by
    intro h
    apply hnv
    rw [Ideal.LiesOver.over (P := P) (p := v.asIdeal), Ideal.under, Ideal.mem_comap]
    simpa using h
  have hyP : y ∉ P := by
    intro h
    apply hbv
    have : algebraMap (𝓞 K) (𝓞 M) b ∈ P :=
      hyb ▸ Ideal.pow_mem_of_mem P h n (Nat.pos_of_ne_zero hn)
    rw [Ideal.LiesOver.over (P := P) (p := v.asIdeal), Ideal.under, Ideal.mem_comap]
    exact this
  have hfP : aeval y (derivative (minpoly (𝓞 K) y)) ∉ P := by
    intro h
    have : (n : 𝓞 M) * y ^ (n - 1) ∈ P := hder ▸ Ideal.mul_mem_right _ P h
    rcases Ideal.IsPrime.mem_or_mem ‹_› this with h1 | h1
    · exact hnP h1
    · exact hyP (Ideal.IsPrime.mem_of_pow_mem ‹_› _ h1)
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K M y hgen'
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  exact hfP (Ideal.le_of_dvd hdvd hmem)

/-- The ramification index form of `isUnramifiedAt_of_pow_eq`. -/
theorem ramificationIdx_eq_one_of_pow_eq {n : ℕ} (a : Kˣ) {α : M}
    (hα : α ^ n = algebraMap K M a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    P.ramificationIdx (𝓞 K) = 1 := by
  have := isUnramifiedAt_of_pow_eq a hα hgen v hnv hav P
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

/-- The `Algebra.IsUnramifiedIn` form of `isUnramifiedAt_of_pow_eq`. -/
theorem isUnramifiedIn_of_pow_eq {n : ℕ} (a : Kˣ) {α : M}
    (hα : α ^ n = algebraMap K M a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal := fun P _ _ =>
  isUnramifiedAt_of_pow_eq a hα hgen v hnv hav P

end KummerRamification

section SUnits

variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable (E : Type u) [Field E] [Algebra F E]

/-- The `S`-units of an extension `E` of `F`: the units `x` with `x` and `x⁻¹` integral over the `S`-integers of `F`. -/
def sUnitsOf : Subgroup Eˣ where
  carrier := {x | IsIntegral (S.integer F) (x : E) ∧ IsIntegral (S.integer F) ((x⁻¹ : Eˣ) : E)}
  mul_mem' hx hy := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact hx.1.mul hy.1
    · rw [mul_inv, Units.val_mul]
      exact hx.2.mul hy.2
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one]
      exact isIntegral_one
    · rw [inv_one, Units.val_one]
      exact isIntegral_one
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable {S E}

/-- Membership in `sUnitsOf S E`. -/
theorem mem_sUnitsOf {x : Eˣ} :
    x ∈ sUnitsOf S E ↔
      IsIntegral (S.integer F) (x : E) ∧ IsIntegral (S.integer F) ((x⁻¹ : Eˣ) : E) :=
  Iff.rfl

/-- Automorphisms of `E / F` preserve integrality over the `S`-integers of `F`. -/
theorem isIntegral_algEquiv_apply (σ : E ≃ₐ[F] E) {x : E} (hx : IsIntegral (S.integer F) x) :
    IsIntegral (S.integer F) (σ x) :=
  hx.map ((σ : E →ₐ[F] E).restrictScalars (S.integer F))

/-- Roots of unity are `S`-units. -/
theorem mem_sUnitsOf_of_mem_rootsOfUnity {n : ℕ} (hn0 : n ≠ 0) {ζ : Eˣ}
    (hζ : ζ ∈ rootsOfUnity n E) : ζ ∈ sUnitsOf S E := by
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have h1 : ∀ y : Eˣ, y ^ n = 1 → IsIntegral (S.integer F) (y : E) := fun y hy =>
    ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, ← Units.val_pow_eq_pow_val,
        hy, Units.val_one, sub_self]⟩
  have hζ' : ζ ^ n = 1 := (mem_rootsOfUnity n ζ).1 hζ
  exact ⟨h1 ζ hζ', h1 ζ⁻¹ (by rw [inv_pow, hζ', inv_one])⟩

/-- The Galois action preserves the `S`-units. -/
theorem galUnitsHom_mem_sUnitsOf (σ : E ≃ₐ[F] E) {x : Eˣ} (hx : x ∈ sUnitsOf S E) :
    galUnitsHom F E σ x ∈ sUnitsOf S E := by
  refine ⟨isIntegral_algEquiv_apply σ hx.1, ?_⟩
  rw [← map_inv]
  exact isIntegral_algEquiv_apply σ hx.2

variable (S E)

/-- The action of `Gal(E / F)` on the `S`-units of `E`. -/
def sUnitsAction : Gal(E/F) →* Monoid.End (sUnitsOf S E) where
  toFun σ := ((galUnitsHom F E σ).comp (sUnitsOf S E).subtype).codRestrict (sUnitsOf S E)
    fun x => galUnitsHom_mem_sUnitsOf σ x.2
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

/-- The action on `S`-units is the Galois action on `E`. -/
@[simp]
theorem coe_sUnitsAction_apply (σ : Gal(E/F)) (x : sUnitsOf S E) :
    (((sUnitsAction S E σ x : Eˣ)) : E) = σ (x : Eˣ) :=
  rfl

/-- The `S`-units of `E`, written additively, as a `Gal(E / F)`-module over `ℤ`. -/
abbrev sUnitsModule : Rep.{u} (ULift.{u} ℤ) Gal(E/F) :=
  Rep.of (intRepOfMonoidEnd.{u} (sUnitsAction S E))

/-- The action on `sUnitsModule S E`. -/
@[simp]
theorem sUnitsModule_ρ_apply (σ : Gal(E/F)) (x : Additive (sUnitsOf S E)) :
    (sUnitsModule S E).ρ σ x = Additive.ofMul (sUnitsAction S E σ x.toMul) :=
  rfl

/-- The inclusion of the `S`-units into the units, as a morphism of Galois modules. -/
def sUnitsToUnits : sUnitsModule S E ⟶ unitsModule F E :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive (sUnitsOf S E).subtype) :
    Additive (sUnitsOf S E) →ₗ[ULift.{u} ℤ] Additive Eˣ), fun σ => by
    ext x
    rfl⟩

/-- `sUnitsToUnits` is the inclusion. -/
@[simp]
theorem sUnitsToUnits_hom_apply (x : Additive (sUnitsOf S E)) :
    (sUnitsToUnits S E).hom x =
      (Additive.ofMul ((Additive.toMul x : sUnitsOf S E) : Eˣ) : unitsModule F E) :=
  rfl

/-- The inclusion of the `S`-units into the units is injective. -/
theorem sUnitsToUnits_injective : Function.Injective (sUnitsToUnits S E).hom := fun _ _ h =>
  Additive.toMul.injective (Subtype.ext (Additive.ofMul.symm.injective h))

/-- The `S`-units of an algebraic extension form a smooth module. -/
instance isSmoothRep_sUnitsModule [Algebra.IsIntegral F E] : IsSmoothRep (sUnitsModule S E) :=
  IsSmoothRep.of_injective (sUnitsToUnits S E) (sUnitsToUnits_injective S E)

variable (n : ℕ) [NeZero n]

/-- The inclusion `μ_n(E) → 𝒪_{E,S}ˣ`. -/
def rootsOfUnityToSUnitsHom : rootsOfUnity n E →* sUnitsOf S E :=
  (rootsOfUnity n E).subtype.codRestrict (sUnitsOf S E) fun ζ =>
    mem_sUnitsOf_of_mem_rootsOfUnity (NeZero.ne n) ζ.2

/-- The inclusion `μ_n(E) → 𝒪_{E,S}ˣ` as a morphism of Galois modules. -/
def rootsOfUnityToSUnits : rootsOfUnityModule F E n ⟶ sUnitsModule S E :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (rootsOfUnityToSUnitsHom S E n)), fun σ => by
    ext x
    rfl⟩

/-- `rootsOfUnityToSUnits` is the inclusion. -/
@[simp]
theorem rootsOfUnityToSUnits_hom_apply (x : Additive (rootsOfUnity n E)) :
    ((((Additive.toMul ((rootsOfUnityToSUnits S E n).hom x) : sUnitsOf S E)) : Eˣ) : E) =
      (((Additive.toMul x : rootsOfUnity n E) : Eˣ) : E) :=
  rfl

end SUnits

section Max

variable (F : Type u) [Field F] [NumberField F] (Ω : Type u) [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- The `S`-units of `K_S`. -/
noncomputable abbrev maximalSUnits : Subgroup (maximalUnramifiedOutside F Ω S)ˣ :=
  sUnitsOf S (maximalUnramifiedOutside F Ω S)

/-- The `S`-units `𝒪_Sˣ` of `K_S` as a `G_S`-module. -/
noncomputable abbrev maximalSUnitsModule : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside F Ω S) :=
  sUnitsModule S (maximalUnramifiedOutside F Ω S)

example [Algebra.IsIntegral F Ω] : IsSmoothRep (maximalSUnitsModule F Ω S) := inferInstance

end Max

section Compare

variable {F : Type u} [Field F] [NumberField F] {L : Type u} [Field L] [NumberField L] [Algebra F L]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- A finite place of `L` lies over the finite place of `F` below it. -/
instance liesOver_under (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal :=
  liesOver_iff_eq_under.2 rfl

/-- At a place of `L` not above `S`, the `S`-integers of `F` have valuation `≤ 1`. -/
theorem valuation_algebraMap_integer_le_one {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ finitePlacesAbove L S)
    (r : S.integer F) : w.valuation L (algebraMap F L r) ≤ 1 := by
  have hv : w.under (𝓞 F) ∉ S := fun h => hw (mem_finitePlacesAbove_iff_under.2 h)
  rw [← valuation_liesOver (K := F) L (w.under (𝓞 F)) w]
  exact pow_le_one₀ zero_le (r.2 _ hv)

/-- An element integral over the `S`-integers of `F` has valuation `≤ 1` at every place of `L` not above `S`. -/
theorem valuation_le_one_of_isIntegral_integer {x : L} (hx : IsIntegral (S.integer F) x)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ finitePlacesAbove L S) : w.valuation L x ≤ 1 :=
  valuation_le_one_of_isIntegral (w.valuation L)
    (fun r => valuation_algebraMap_integer_le_one S hw r) hx

/-- Conversely, an element of `L` with valuation `≤ 1` at every place not above `S` is integral over the `S`-integers of `F`. -/
theorem isIntegral_integer_of_valuation_le_one {x : L}
    (h : ∀ w ∉ finitePlacesAbove L S, w.valuation L x ≤ 1) : IsIntegral (S.integer F) x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx0
  · exact isIntegral_zero
  have hT : (Support (𝓞 L) x).Finite := Support.finite (𝓞 L) x
  have hTS : ∀ w ∈ Support (𝓞 L) x, w.under (𝓞 F) ∈ S := fun w hw => by
    by_contra hn
    exact (not_lt.2 (h w fun hm => hn (mem_finitePlacesAbove_iff_under.1 hm))) hw
  let V : Finset (HeightOneSpectrum (𝓞 F)) := hT.toFinset.image fun w => w.under (𝓞 F)
  let π : HeightOneSpectrum (𝓞 F) → 𝓞 F := fun v =>
    (exists_pow_classNumber_eq_span v).choose
  let t : Fˣ := ∏ v ∈ V, placeUnit v
  have htS : t ∈ S.unit F := Subgroup.prod_mem _ fun v hv => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    exact placeUnit_mem S (hTS w (hT.mem_toFinset.1 hw))
  have ht₀ : (t : F) = algebraMap (𝓞 F) F (∏ v ∈ V, π v) := by
    simp only [t, Units.coe_prod, map_prod]
    rfl
  have hπ : ∀ v, π v ∈ v.asIdeal := fun v => by
    have h1 : π v ∈ Ideal.span {π v} := Ideal.mem_span_singleton_self _
    rw [← (exists_pow_classNumber_eq_span v).choose_spec.2] at h1
    exact Ideal.pow_le_self Fintype.card_ne_zero h1
  have hwt : ∀ w ∈ Support (𝓞 L) x, w.valuation L (algebraMap F L t) < 1 := by
    intro w hw
    have hv : w.under (𝓞 F) ∈ V := Finset.mem_image_of_mem _ (hT.mem_toFinset.2 hw)
    have hmem : ∏ v ∈ V, π v ∈ (w.under (𝓞 F)).asIdeal := by
      rw [← Finset.mul_prod_erase V π hv]
      exact Ideal.mul_mem_right _ _ (hπ _)
    have hmem' : algebraMap (𝓞 F) (𝓞 L) (∏ v ∈ V, π v) ∈ w.asIdeal := hmem
    rw [ht₀, ← IsScalarTower.algebraMap_apply (𝓞 F) F L,
      IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L, valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem w _).2 hmem'
  have hwt1 : ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L (algebraMap F L t) ≤ 1 := by
    intro w
    rw [ht₀, ← IsScalarTower.algebraMap_apply (𝓞 F) F L,
      IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L]
    exact w.valuation_le_one _
  have ht0 : algebraMap F L t ≠ 0 := (_root_.map_ne_zero _).2 t.ne_zero
  have hN : ∀ w : HeightOneSpectrum (𝓞 L), ∃ N : ℕ, w ∈ Support (𝓞 L) x →
      w.valuation L x * w.valuation L (algebraMap F L t) ^ N ≤ 1 := by
    intro w
    by_cases hw : w ∈ Support (𝓞 L) x
    · obtain ⟨N, hN⟩ := exists_mul_pow_le_one ((_root_.map_ne_zero (w.valuation L)).2 ht0) (hwt w hw)
        ((_root_.map_ne_zero (w.valuation L)).2 hx0)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose Nw hNw using hN
  let N := ∑ w ∈ hT.toFinset, Nw w
  let y := algebraMap F L t ^ N * x
  have hy : ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L y ≤ 1 := by
    intro w
    simp only [y, map_mul, map_pow]
    by_cases hw : w ∈ Support (𝓞 L) x
    · have hle : Nw w ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hT.mem_toFinset.2 hw)
      rw [mul_comm]
      exact (mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' (hwt1 w) hle)).trans
        (hNw w hw)
    · have hx1 : w.valuation L x ≤ 1 := not_lt.1 hw
      exact mul_le_one' (pow_le_one₀ zero_le (hwt1 w)) hx1
  obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one (R := 𝓞 L) L y hy
  have hyI : IsIntegral (S.integer F) y := by
    rw [← hb]
    exact (RingOfIntegers.isIntegral_coe b).tower_top
  have hc : (((t⁻¹ ^ N : Fˣ)) : F) ∈ S.integer F := fun v hv =>
    (Subgroup.pow_mem _ (inv_mem htS) N v hv).le
  have hxy : x = algebraMap (S.integer F) L ⟨_, hc⟩ * y := by
    change x = algebraMap F L (((t⁻¹ ^ N : Fˣ)) : F) * (algebraMap F L t ^ N * x)
    rw [← mul_assoc, ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      inv_pow, inv_mul_cancel, Units.val_one, map_one, one_mul]
  rw [hxy]
  exact isIntegral_algebraMap.mul hyI

/-- The `S`-units of a number field `L` over `F` are Mathlib's `S_L`-units, `S_L` the places of `L` above `S`. -/
theorem mem_sUnitsOf_iff_mem_unit {x : Lˣ} :
    x ∈ sUnitsOf S L ↔ x ∈ (finitePlacesAbove L S).unit L := by
  constructor
  · intro hx w hw
    have h1 := valuation_le_one_of_isIntegral_integer S hx.1 hw
    have h2 := valuation_le_one_of_isIntegral_integer S hx.2 hw
    refine eq_one_of_one_le_mul_left h1 h2 (Eq.ge ?_)
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  · intro hx
    exact ⟨isIntegral_integer_of_valuation_le_one S fun w hw =>
        (hx w hw).le,
      isIntegral_integer_of_valuation_le_one S fun w hw =>
        (inv_mem hx w hw).le⟩

end Compare

section Invariants

variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable (E : Type u) [Field E] [Algebra F E]

/-- `S`-integers of `F` stay integral in `E`. -/
theorem isIntegral_algebraMap_of_mem_integer {c : F} (hc : c ∈ S.integer F) :
    IsIntegral (S.integer F) (algebraMap F E c) :=
  isIntegral_algebraMap (x := (⟨c, hc⟩ : S.integer F))

/-- An element of `F` integral in `E` over the `S`-integers is integral in `F`. -/
theorem isIntegral_of_isIntegral_algebraMap {c : F}
    (hc : IsIntegral (S.integer F) (algebraMap F E c)) : IsIntegral (S.integer F) c :=
  (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars (S.integer F))
    (algebraMap F E).injective).1 hc

/-- The `S`-integers of `F` are integrally closed in `F`. -/
theorem mem_integer_of_isIntegral {c : F} (hc : IsIntegral (S.integer F) c) : c ∈ S.integer F :=
  fun v _ => valuation_le_one_of_isIntegral (v.valuation F) (fun r => r.2 v ‹_›) hc

variable {E} in

/-- A unit of `F` is an `S`-unit of `E` exactly when it is an `S`-unit of `F`. -/
theorem map_mem_sUnitsOf_iff {a : Fˣ} :
    Units.map (algebraMap F E : F →* E) a ∈ sUnitsOf S E ↔ a ∈ S.unit F := by
  constructor
  · intro h v hv
    have h1 : (a : F) ∈ S.integer F :=
      mem_integer_of_isIntegral S (isIntegral_of_isIntegral_algebraMap S E h.1)
    have h2 : ((a⁻¹ : Fˣ) : F) ∈ S.integer F := by
      refine mem_integer_of_isIntegral S (isIntegral_of_isIntegral_algebraMap S E ?_)
      have := h.2
      rwa [← map_inv] at this
    refine eq_one_of_one_le_mul_left (h1 v hv) (h2 v hv) (Eq.ge ?_)
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  · intro h
    refine ⟨isIntegral_algebraMap_of_mem_integer S E fun v hv => (h v hv).le, ?_⟩
    rw [← map_inv]
    exact isIntegral_algebraMap_of_mem_integer S E fun v hv => (inv_mem h v hv).le

/-- The `S`-units of `F` as invariants of the `S`-units of `E`. -/
def sUnitsToInvariants : Additive (S.unit F) →+ (sUnitsModule S E).ρ.invariants where
  toFun a := ⟨Additive.ofMul ⟨Units.map (algebraMap F E : F →* E) (Additive.toMul a : S.unit F),
      (map_mem_sUnitsOf_iff S).2 (Additive.toMul a).2⟩, fun σ =>
    Additive.toMul.injective (Subtype.ext (Units.ext (σ.commutes _)))⟩
  map_zero' := Subtype.ext (Additive.toMul.injective (Subtype.ext (Units.ext (map_one _))))
  map_add' _ _ := Subtype.ext (Additive.toMul.injective (Subtype.ext (Units.ext (map_mul _ _ _))))

/-- `sUnitsToInvariants` is the inclusion `F → E`. -/
@[simp]
theorem coe_sUnitsToInvariants_apply (a : Additive (S.unit F)) :
    (((Additive.toMul (α := sUnitsOf S E) (sUnitsToInvariants S E a).1 : sUnitsOf S E) : Eˣ) : E) =
      algebraMap F E ((Additive.toMul a : S.unit F) : Fˣ) :=
  rfl

/-- `sUnitsToInvariants` is injective. -/
theorem sUnitsToInvariants_injective : Function.Injective (sUnitsToInvariants S E) := by
  intro a b h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact (algebraMap F E).injective (congrArg (fun v : (sUnitsModule S E).ρ.invariants =>
    (((Additive.toMul (α := sUnitsOf S E) v.1 : sUnitsOf S E) : Eˣ) : E)) h)

/-- For `E / F` Galois, every invariant `S`-unit of `E` comes from `F`. -/
theorem sUnitsToInvariants_surjective [IsGalois F E] :
    Function.Surjective (sUnitsToInvariants S E) := by
  intro v
  let u : Eˣ := ((Additive.toMul (α := sUnitsOf S E) v.1 : sUnitsOf S E) : Eˣ)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (u : E)).2 fun σ =>
    congrArg (fun w : Additive (sUnitsOf S E) =>
      (((Additive.toMul w : sUnitsOf S E) : Eˣ) : E)) (v.2 σ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact u.ne_zero ha.symm
  have hmap : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = u := Units.ext ha
  have hS : Units.mk0 a ha0 ∈ S.unit F := by
    rw [← map_mem_sUnitsOf_iff S (E := E), hmap]
    exact (Additive.toMul (α := sUnitsOf S E) v.1).2
  exact ⟨Additive.ofMul ⟨Units.mk0 a ha0, hS⟩,
    Subtype.ext (Additive.toMul.injective (Subtype.ext hmap))⟩

/-- For `E / F` Galois, `(𝒪_{E,S}ˣ)^{Gal(E/F)} = 𝒪_{F,S}ˣ`. -/
noncomputable def sUnitsInvariantsEquiv [IsGalois F E] :
    Additive (S.unit F) ≃+ (sUnitsModule S E).ρ.invariants :=
  AddEquiv.ofBijective (sUnitsToInvariants S E)
    ⟨sUnitsToInvariants_injective S E, sUnitsToInvariants_surjective S E⟩

/-- `sUnitsInvariantsEquiv` is `sUnitsToInvariants`. -/
@[simp]
theorem sUnitsInvariantsEquiv_apply [IsGalois F E] (a : Additive (S.unit F)) :
    sUnitsInvariantsEquiv S E a = sUnitsToInvariants S E a :=
  rfl

/-- `H⁰(Gal(E/F), 𝒪_{E,S}ˣ) ≅ 𝒪_{F,S}ˣ` for `E / F` Galois. -/
noncomputable def cohomologyZeroSUnitsEquiv [IsGalois F E] :
    cohomology (sUnitsModule S E) 0 ≃+ Additive (S.unit F) :=
  (zeroIso (sUnitsModule S E)).toLinearEquiv.toAddEquiv.trans (sUnitsInvariantsEquiv S E).symm

end Invariants

section Max

variable (F : Type u) [Field F] [NumberField F] (Ω : Type u) [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- For `L ⊆ K_S`, a unit of `L` is an `S`-unit of `K_S` exactly when it is an `S`-unit of `L`. -/
theorem map_inclusion_mem_maximalSUnits_iff {L : IntermediateField F Ω}
    (hL : L ≤ maximalUnramifiedOutside F Ω S) {x : Lˣ} :
    Units.map (IntermediateField.inclusion hL : L →* maximalUnramifiedOutside F Ω S) x ∈
      maximalSUnits F Ω S ↔ x ∈ sUnitsOf S L := by
  let f := (IntermediateField.inclusion hL).restrictScalars (S.integer F)
  have hf : Function.Injective f := (IntermediateField.inclusion hL).toRingHom.injective
  constructor
  · intro h
    refine ⟨(isIntegral_algHom_iff f hf).1 h.1, (isIntegral_algHom_iff f hf).1 ?_⟩
    have := h.2
    rwa [← map_inv] at this
  · intro h
    refine ⟨(isIntegral_algHom_iff f hf).2 h.1, ?_⟩
    rw [← map_inv]
    exact (isIntegral_algHom_iff f hf).2 h.2

variable [IsGalois F Ω]

/-- Every `S`-unit of `K_S` is an `S`-unit of a finite subextension. -/
theorem exists_of_mem_maximalSUnits {y : (maximalUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ maximalSUnits F Ω S) :
    ∃ (L : IntermediateField F Ω) (_ : FiniteDimensional F L)
      (hL : L ≤ maximalUnramifiedOutside F Ω S) (x : Lˣ), x ∈ sUnitsOf S L ∧
        Units.map (IntermediateField.inclusion hL : L →* maximalUnramifiedOutside F Ω S) x = y := by
  obtain ⟨L, hf, hu, hmem⟩ :=
    (mem_maximalUnramifiedOutside_iff S).1 (y : maximalUnramifiedOutside F Ω S).2
  have hL := le_maximalUnramifiedOutside S hu
  have hx0 : (⟨_, hmem⟩ : L) ≠ 0 := by
    intro h
    apply y.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  have hmap : Units.map (IntermediateField.inclusion hL : L →* maximalUnramifiedOutside F Ω S)
      (Units.mk0 _ hx0) = y := Units.ext rfl
  refine ⟨L, hf, hL, Units.mk0 _ hx0, ?_, hmap⟩
  rw [← map_inclusion_mem_maximalSUnits_iff F Ω S hL, hmap]
  exact hy

end Max

section Roots

variable {F : Type u} [Field F] [NumberField F] {Ω : Type u} [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- `L(α)` is generated over `L` by the element `α` of itself. -/
theorem adjoin_gen_eq_top (L : Type u) [Field L] [Algebra L Ω] (α : Ω) :
    IntermediateField.adjoin L {IntermediateField.AdjoinSimple.gen L α} = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin L {α}).val
  rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.val_mk,
    IntermediateField.AdjoinSimple.coe_gen, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]

variable [IsGalois F Ω]

/-- If `n` is invertible outside `S`, an `n`-th root of an `S`-unit of `K_S` lies in `K_S`. -/
theorem mem_maximalUnramifiedOutside_of_pow_eq {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {y : (maximalUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ maximalSUnits F Ω S) {α : Ω} (hα : α ^ n = ((y : maximalUnramifiedOutside F Ω S) : Ω)) :
    α ∈ maximalUnramifiedOutside F Ω S := by
  obtain ⟨L, hfin, hLle, x, hxS, rfl⟩ := exists_of_mem_maximalSUnits F Ω S hy
  have : NumberField L := NumberField.of_module_finite F L
  have hxU := (mem_sUnitsOf_iff_mem_unit S).1 hxS
  have hLu : IsUnramifiedOutside S L := (isUnramifiedOutside_iff_le S).2 hLle
  have hα' : α ^ n = algebraMap L Ω (x : L) := hα
  have hαint : IsIntegral L α := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hα']
    exact isIntegral_algebraMap
  let M : IntermediateField L Ω := IntermediateField.adjoin L {α}
  have : FiniteDimensional L M := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField M := NumberField.of_module_finite L M
  have hgen : α ^ n = algebraMap L Ω (x : L) := hα'
  have hβ : IntermediateField.AdjoinSimple.gen L α ^ n = algebraMap L M (x : L) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hgen]
    rfl
  have hMu : IsUnramifiedOutside (finitePlacesAbove L S) M := by
    intro w hw
    refine isUnramifiedIn_of_pow_eq x hβ (adjoin_gen_eq_top L α) w ?_ ?_
    · intro hmem
      have hv : w.under (𝓞 F) ∉ S := fun h => hw (mem_finitePlacesAbove_iff_under.2 h)
      apply hnS _ hv
      change ((n : ℕ) : 𝓞 F) ∈ Ideal.comap (algebraMap (𝓞 F) (𝓞 L)) w.asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hmem
    · rw [hxU w hw, WithZero.log_one]
      exact dvd_zero _
  have hMF := (isUnramifiedOutside_restrictScalars_iff S hLu M).2 hMu
  have : FiniteDimensional F (M.restrictScalars F) := FiniteDimensional.trans F L M
  exact le_maximalUnramifiedOutside S hMF (IntermediateField.mem_adjoin_simple_self L α)

/-- If `n` is invertible outside `S`, the `n`-th roots of unity lie in `K_S`. -/
theorem mem_maximalUnramifiedOutside_of_pow_eq_one {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {ζ : Ω} (hζ : ζ ^ n = 1) :
    ζ ∈ maximalUnramifiedOutside F Ω S :=
  mem_maximalUnramifiedOutside_of_pow_eq S hn hnS (maximalSUnits F Ω S).one_mem hζ

/-- A unit whose `n`-th power is an `S`-unit is an `S`-unit. -/
theorem mem_sUnitsOf_of_pow_mem (E : Type u) [Field E] [Algebra F E] {n : ℕ} (hn : n ≠ 0)
    {β : Eˣ} (hβ : β ^ n ∈ sUnitsOf S E) : β ∈ sUnitsOf S E := by
  refine ⟨IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_, IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_⟩
  · rw [← Units.val_pow_eq_pow_val]
    exact hβ.1
  · rw [← Units.val_pow_eq_pow_val, inv_pow]
    exact hβ.2

variable [IsSepClosed Ω]

/-- If `n` is invertible outside `S` and `Ω` is separably closed, every `S`-unit of `K_S` is an `n`-th power of an `S`-unit of `K_S`. -/
theorem exists_pow_eq_of_mem_maximalSUnits {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {y : (maximalUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ maximalSUnits F Ω S) : ∃ β ∈ maximalSUnits F Ω S, β ^ n = y := by
  have : NeZero ((n : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap F Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)⟩
  obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq
    (((y : maximalUnramifiedOutside F Ω S) : Ω)) n
  have hαS := mem_maximalUnramifiedOutside_of_pow_eq S hn hnS hy hα
  have hα0 : (⟨α, hαS⟩ : maximalUnramifiedOutside F Ω S) ≠ 0 := by
    intro h
    have h' : α = 0 := congrArg Subtype.val h
    rw [h', zero_pow hn] at hα
    exact y.ne_zero (Subtype.ext hα.symm)
  have hpow : Units.mk0 _ hα0 ^ n = y := Units.ext (Subtype.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow]
    exact hα))
  refine ⟨Units.mk0 _ hα0, mem_sUnitsOf_of_pow_mem S _ hn (hpow ▸ hy), hpow⟩

end Roots

end

end Langlands.GaloisCohomology

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section RootsOfUnityCount

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (N : ℕ) [NeZero N]

attribute [local instance 2000] IsSepClosure.isGalois

/-- `K_S` contains `N` distinct `N`-th roots of unity when the places above `N` are in `S`. -/
theorem card_rootsOfUnity_maximalUnramifiedOutside
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Nat.card (rootsOfUnity N (maximalUnramifiedOutside K Ω S)) = N := by
  have hN : N ≠ 0 := NeZero.ne N
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hK : ((N : ℕ) : K) ≠ 0 := by exact_mod_cast hN
  have : NeZero ((N : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero _).mpr hK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω N
  have hmem : ζ ∈ maximalUnramifiedOutside K Ω S :=
    mem_maximalUnramifiedOutside_of_pow_eq_one S hN (fun w hw h => hw (hS w h)) hζ.pow_eq_one
  have hζS : IsPrimitiveRoot (⟨ζ, hmem⟩ : maximalUnramifiedOutside K Ω S) N :=
    IsPrimitiveRoot.of_map_of_injective (f := (maximalUnramifiedOutside K Ω S).val) hζ
      (maximalUnramifiedOutside K Ω S).val.injective
  exact hζS.card_rootsOfUnity

end RootsOfUnityCount

section PrimitiveRoot

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (q : ℕ) [NeZero q]

omit [Finite S] in
/-- With the places above `q` in `S`, `K_S` contains a primitive `q`-th root of unity. -/
theorem exists_isPrimitiveRoot_mem
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ q ∧ ζ ∈ maximalUnramifiedOutside K Ω S := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  have : NeZero (q : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne q)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω q
  exact ⟨ζ, hζ, mem_maximalUnramifiedOutside_of_pow_eq_one S (NeZero.ne q)
    (fun v hv h => hv (hS v h)) hζ.pow_eq_one⟩

end PrimitiveRoot

end

end Langlands.GaloisCohomology
