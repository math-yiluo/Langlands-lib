import Langlands.Algebra.RenardLocalizationStabilityStatements
import Langlands.Algebra.RenardEndomorphismLocalizationKernelProof
import Langlands.LinearAlgebra.NoetherianLocalizationCoreProof

/-!
# Proof of actual-localization stability and the canonical stable image

Internal ordinary-unital-module results motivated by Renard 2026,
Appendix C.II, printed page 279 / PDF page 285. The Noetherian part uses the
published internal Noetherian core; the stable-image part is a direct Fitting
argument and needs no finiteness hypothesis.
-/

set_option autoImplicit false

universe uR uV

namespace Langlands.Renard.EndomorphismLocalization

namespace StabilityProof

open Langlands.LinearAlgebra.NoetherianLocalizationCore

section General

variable {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]

theorem localizedEquiv_pow_apply (a : Module.End R V) (m : ℕ) (z : Localized a) :
    (localizedEquiv a ^ m) z = (localizedEnd a ^ m) z := by
  rw [LinearEquiv.pow_apply, Module.End.pow_apply]
  rfl

/-- `ι (aᵐ x) = ãᵐ (ι x)`. -/
theorem iota_pow_apply (a : Module.End R V) (m : ℕ) (x : V) :
    iota a ((a ^ m) x) = (localizedEnd a ^ m) (iota a x) := by
  rw [intertwines_pow a (localizedEquiv a) (iota a) (fun v => iota_intertwines a v) m x,
    localizedEquiv_pow_apply]

/-- Every element of the actual localization becomes canonical after a power of `ã`. -/
theorem power_exhaustion (a : Module.End R V) (y : Localized a) :
    ∃ (m : ℕ) (x : V), (localizedEquiv a ^ m) y = iota a x := by
  obtain ⟨v, m, rfl⟩ := frac_surjective a y
  exact ⟨m, v, by rw [localizedEquiv_pow_apply, localizedEnd_pow_frac]⟩

/-- The Noetherian conclusion, from the published internal Noetherian core. -/
theorem noetherian_actual (a : Module.End R V) [IsNoetherian R V]
    [IsNoetherian R (Localized a)] :
    Function.Surjective (iota a) ∧
      ∃ n : ℕ, 0 < n ∧
        LinearMap.ker (iota a) = LinearMap.ker (a ^ n) ∧
        LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2) ∧
        LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2) :=
  localization_core a (localizedEquiv a) (iota a) (fun v => iota_intertwines a v)
    (power_exhaustion a) (fun x hx => (iota_eq_zero_iff a x).mp hx)

end General

section Stable

variable {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]
  (a : Module.End R V) {n : ℕ}

/-- With `0 < n` and `ker aⁿ = ker a²ⁿ`, `aⁿ⁺¹ x = 0` forces `aⁿ x = 0`. -/
theorem pow_apply_eq_zero_of_succ (hn : 0 < n)
    (hk : LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2))
    {x : V} (hx : (a ^ (n + 1)) x = 0) : (a ^ n) x = 0 := by
  have h2 : x ∈ LinearMap.ker ((a ^ n) ^ 2) := by
    rw [LinearMap.mem_ker, ← pow_mul, show n * 2 = (n - 1) + (n + 1) by omega, pow_add,
      Module.End.mul_apply, hx, map_zero]
  rw [← hk] at h2
  exact LinearMap.mem_ker.mp h2

/-- With `0 < n` and `ker aⁿ = ker a²ⁿ`, every power kernel of `a` lies in `ker aⁿ`. -/
theorem pow_apply_eq_zero_of_pow (hn : 0 < n)
    (hk : LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2))
    (m : ℕ) {x : V} (hx : (a ^ m) x = 0) : (a ^ n) x = 0 := by
  have key : ∀ k : ℕ, ∀ y : V, (a ^ (n + k)) y = 0 → (a ^ n) y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa only [add_zero] using hy
    | succ k ih =>
      intro y hy
      apply pow_apply_eq_zero_of_succ a hn hk
      have hy' : (a ^ (n + k)) (a y) = 0 := by
        rw [← Module.End.mul_apply, ← pow_succ, add_assoc]
        exact hy
      have h := ih (a y) hy'
      rw [pow_succ, Module.End.mul_apply]
      exact h
  apply key m x
  rw [pow_add, Module.End.mul_apply, hx, map_zero]

/-- The Fitting decomposition at a positive stable exponent. -/
theorem isCompl_ker_range (hk : LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2))
    (hr : LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2)) :
    IsCompl (LinearMap.ker (a ^ n)) (LinearMap.range (a ^ n)) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have hy : y ∈ LinearMap.ker ((a ^ n) ^ 2) := by
      rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply]
      exact LinearMap.mem_ker.mp hx
    rw [← hk] at hy
    exact LinearMap.mem_ker.mp hy
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : (a ^ n) v ∈ LinearMap.range ((a ^ n) ^ 2) := by
      rw [← hr]
      exact LinearMap.mem_range_self _ v
    obtain ⟨w, hw⟩ := hv
    have hker : v - (a ^ n) w ∈ LinearMap.ker (a ^ n) := by
      rw [LinearMap.mem_ker, map_sub, ← hw, pow_two, Module.End.mul_apply, sub_self]
    simpa only [sub_add_cancel] using
      Submodule.add_mem_sup hker (LinearMap.mem_range_self (a ^ n) w)

/-- The stable image is `a`-invariant. -/
theorem apply_mem_range {x : V} (hx : x ∈ LinearMap.range (a ^ n)) :
    a x ∈ LinearMap.range (a ^ n) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨a y, ?_⟩
  change (a ^ n * a) y = (a * a ^ n) y
  rw [← pow_succ, ← pow_succ']

/-- With `0 < n` and `im aⁿ = im a²ⁿ`, `a` maps the stable image onto itself. -/
theorem exists_apply_eq (hn : 0 < n)
    (hr : LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2))
    {s : V} (hs : s ∈ LinearMap.range (a ^ n)) :
    ∃ t ∈ LinearMap.range (a ^ n), a t = s := by
  rw [hr] at hs
  obtain ⟨w, rfl⟩ := hs
  refine ⟨(a ^ n) ((a ^ (n - 1)) w), LinearMap.mem_range_self _ _, ?_⟩
  rw [← pow_mul, show n * 2 = 1 + (n + (n - 1)) by omega, pow_add, pow_add, pow_one,
    Module.End.mul_apply, Module.End.mul_apply]

/-- Every power of `a` maps the stable image onto itself. -/
theorem exists_pow_apply_eq (hn : 0 < n)
    (hr : LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2)) (m : ℕ) :
    ∀ {s : V}, s ∈ LinearMap.range (a ^ n) →
      ∃ t ∈ LinearMap.range (a ^ n), (a ^ m) t = s := by
  induction m with
  | zero => exact fun {s} hs => ⟨s, hs, by rw [pow_zero, Module.End.one_apply]⟩
  | succ m ih =>
    intro s hs
    obtain ⟨t, ht, rfl⟩ := exists_apply_eq a hn hr hs
    obtain ⟨u, hu, rfl⟩ := ih ht
    exact ⟨u, hu, by rw [pow_succ', Module.End.mul_apply]⟩

/-- No nonzero element of the stable image is killed by a power of `a`. -/
theorem eq_zero_of_pow_apply_eq_zero (hn : 0 < n)
    (hk : LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2))
    {s : V} (hs : s ∈ LinearMap.range (a ^ n)) (k : ℕ) (h : (a ^ k) s = 0) : s = 0 := by
  obtain ⟨y, rfl⟩ := hs
  apply pow_apply_eq_zero_of_pow a hn hk (k + n)
  rw [pow_add, Module.End.mul_apply]
  exact h

/-- The restriction of `ι` to the stable image is injective. -/
theorem iota_comp_subtype_injective (hn : 0 < n)
    (hk : LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2)) :
    Function.Injective ((iota a).comp (LinearMap.range (a ^ n)).subtype) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro s hs
  obtain ⟨k, hks⟩ := (iota_eq_zero_iff a s).mp hs
  exact Subtype.ext (eq_zero_of_pow_apply_eq_zero a hn hk s.2 k hks)

/-- The restriction of `ι` to the stable image is surjective. -/
theorem iota_comp_subtype_surjective (hn : 0 < n)
    (hk : LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2))
    (hr : LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2)) :
    Function.Surjective ((iota a).comp (LinearMap.range (a ^ n)).subtype) := by
  intro y
  obtain ⟨v, m, rfl⟩ := frac_surjective a y
  have hv : v ∈ LinearMap.ker (a ^ n) ⊔ LinearMap.range (a ^ n) := by
    rw [(isCompl_ker_range a hk hr).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨k0, hk0, s0, hs0, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨t, ht, rfl⟩ := exists_pow_apply_eq a hn hr m hs0
  refine ⟨⟨t, ht⟩, ?_⟩
  change iota a t = frac a (k0 + (a ^ m) t) m
  apply (localizedEquiv a ^ m).injective
  rw [localizedEquiv_pow_apply, localizedEquiv_pow_apply, localizedEnd_pow_frac, map_add,
    (iota_eq_zero_iff a k0).mpr ⟨n, LinearMap.mem_ker.mp hk0⟩, zero_add, iota_pow_apply]

/-- A positive stable exponent gives the canonical stable-image identification. -/
theorem stablePowerImageAt_of_stable (hn : 0 < n)
    (hk : LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2))
    (hr : LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2)) :
    StablePowerImageAt a n := by
  let g : LinearMap.range (a ^ n) →ₗ[R] Localized a :=
    (iota a).comp (LinearMap.range (a ^ n)).subtype
  have hg : Function.Bijective g :=
    ⟨iota_comp_subtype_injective a hn hk, iota_comp_subtype_surjective a hn hk hr⟩
  let e : Localized a ≃ₗ[R] LinearMap.range (a ^ n) := (LinearEquiv.ofBijective g hg).symm
  have he_symm : ∀ s, e.symm s = iota a s := fun s => rfl
  have he : e.symm.toLinearMap = (iota a).comp (LinearMap.range (a ^ n)).subtype :=
    LinearMap.ext fun s => he_symm s
  refine ⟨isCompl_ker_range a hk hr, e, ⟨LinearMap.ext fun z => ?_, he⟩, ?_⟩
  · have hmem : a (e z : V) ∈ LinearMap.range (a ^ n) := apply_mem_range a (e z).2
    have key : e (localizedEnd a z) = ⟨a (e z), hmem⟩ := by
      apply e.symm.injective
      rw [LinearEquiv.symm_apply_apply, he_symm]
      change localizedEnd a z = iota a (a (e z))
      rw [iota_intertwines, ← he_symm, LinearEquiv.symm_apply_apply]
    change ((e (localizedEnd a z) : LinearMap.range (a ^ n)) : V) = a (e z)
    rw [key]
  · rintro e' ⟨-, he'⟩
    exact LinearEquiv.symm_bijective.injective
      (LinearEquiv.toLinearMap_injective (he'.trans he.symm))

end Stable

end StabilityProof

open StabilityProof

/-- Noetherian source and actual localization: surjectivity of `ι` and one common positive
stable exponent. -/
theorem noetherianActualLocalizationStatement :
    NoetherianActualLocalizationStatement.{uR, uV} := by
  intro R _ V _ _ a hV hL
  exact noetherian_actual a

/-- Every positive stable exponent gives the canonical stable-image identification. -/
theorem stablePowerImageStatement : StablePowerImageStatement.{uR, uV} := by
  intro R _ V _ _ a n hn hk hr
  exact stablePowerImageAt_of_stable a hn hk hr

/-- The finite-module specialization over a Noetherian commutative ring. -/
theorem finiteActualLocalizationStatement : FiniteActualLocalizationStatement.{uR, uV} := by
  intro R _ V _ _ a hR hV hL
  have := isNoetherian_of_isNoetherianRing_of_finite R V
  have := isNoetherian_of_isNoetherianRing_of_finite R (Localized a)
  obtain ⟨hsurj, hexp⟩ := noetherian_actual a
  exact ⟨hsurj, hexp, fun n hn hk hr => stablePowerImageAt_of_stable a hn hk hr⟩

/-- The complete internal ordinary-module actual-localization stability statement family. -/
theorem actualLocalizationStabilityStatements :
    ActualLocalizationStabilityStatements.{uR, uV} :=
  ⟨noetherianActualLocalizationStatement, stablePowerImageStatement,
    finiteActualLocalizationStatement⟩

end Langlands.Renard.EndomorphismLocalization
