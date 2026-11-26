import Langlands.Representation.Clifford.Twist
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant normalization of extensions
-/

noncomputable section

namespace Langlands.Clifford

open Representation

universe uG uV

section CommGroupPowers

variable {M : Type*} [CommGroup M]

/-- An element killed by two coprime exponents is trivial. -/
theorem eq_one_of_pow_coprime {x : M} {a b : ℕ} (hab : Nat.Coprime a b) (ha : x ^ a = 1)
    (hb : x ^ b = 1) : x = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨ha, hb⟩
  rwa [hab, pow_one] at h

/-- An element of order dividing `m` has a `k`-th root in its own powers when `k` is prime to
`m`. -/
theorem exists_zpow_pow_eq {y : M} {m k : ℕ} (hy : y ^ m = 1) (hmk : Nat.Coprime k m) :
    ∃ u : ℤ, (y ^ u) ^ k = y := by
  obtain ⟨u, v, huv⟩ := (Nat.Coprime.isCoprime hmk)
  refine ⟨u, ?_⟩
  have hym : y ^ (m : ℤ) = 1 := by rw [zpow_natCast, hy]
  calc (y ^ u) ^ k = y ^ (u * k) := by rw [← zpow_natCast, ← zpow_mul]
    _ = y ^ (u * k + v * m) * (y ^ (m : ℤ)) ^ (-v) := by
        rw [← zpow_mul, ← zpow_add]
        congr 1
        ring
    _ = y := by rw [huv, zpow_one, hym, one_zpow, mul_one]

/-- An element killed by `p ^ s * m`, with `p ^ s` and `m` coprime, is the product of a power of
it killed by `p ^ s` and a power of it killed by `m`. -/
theorem exists_split {x : M} {s m : ℕ} {p : ℕ} (hx : x ^ (p ^ s * m) = 1)
    (hm : Nat.Coprime (p ^ s) m) :
    ∃ u v : ℤ, x = x ^ u * x ^ v ∧ (x ^ u) ^ (p ^ s) = 1 ∧ (x ^ v) ^ m = 1 := by
  obtain ⟨a, b, hab⟩ := Nat.Coprime.isCoprime hm
  have hx' : x ^ (((p ^ s * m : ℕ)) : ℤ) = 1 := by rw [zpow_natCast, hx]
  refine ⟨b * m, a * (p ^ s : ℕ), ?_, ?_, ?_⟩
  · rw [← zpow_add, show b * (m : ℤ) + a * ((p ^ s : ℕ) : ℤ) = 1 by linarith, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul,
      show b * (m : ℤ) * ((p ^ s : ℕ) : ℤ) = ((p ^ s * m : ℕ) : ℤ) * b by push_cast; ring,
      zpow_mul, hx', one_zpow]
  · rw [← zpow_natCast, ← zpow_mul,
      show a * ((p ^ s : ℕ) : ℤ) * (m : ℤ) = ((p ^ s * m : ℕ) : ℤ) * a by push_cast; ring,
      zpow_mul, hx', one_zpow]

end CommGroupPowers

section Det

variable {H : Type uG} [Group H] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The determinant character `h ↦ det (θ h)`, used for finite-dimensional representations. -/
def detChar (θ : Representation ℂ H V) : H →* ℂˣ :=
  (Units.map (LinearMap.det : Module.End ℂ V →* ℂ)).comp θ.asGroupHom

theorem detChar_apply (θ : Representation ℂ H V) (h : H) :
    (detChar θ h : ℂ) = LinearMap.det (θ h) := rfl

/-- Twisting multiplies the determinant by the character raised to the dimension. -/
theorem detChar_twist [FiniteDimensional ℂ V] (χ : H →* ℂˣ) (θ : Representation ℂ H V) :
    detChar (Langlands.twist χ θ) = χ ^ Module.finrank ℂ V * detChar θ := by
  ext h
  change LinearMap.det ((χ h : ℂ) • θ h) = _
  rw [LinearMap.det_smul]
  simp [detChar_apply]

/-- Equivalent finite-dimensional representations have the same determinant. -/
theorem detChar_eq_of_equiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] {θ : Representation ℂ H V} {σ : Representation ℂ H W}
    (e : θ.Equiv σ) : detChar θ = detChar σ := by
  ext h
  change LinearMap.det (θ h) = LinearMap.det (σ h)
  have hc : e.toLinearMap ∘ₗ θ h ∘ₗ e.symm.toLinearMap = σ h := by
    ext b
    simpa using Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap h
      (e.symm b)
  rw [← LinearMap.det_conj (θ h) e.toLinearEquiv]
  exact congrArg LinearMap.det hc

theorem detChar_comp {H' : Type*} [Group H'] (θ : Representation ℂ H V) (f : H' →* H) :
    detChar (θ.comp f) = (detChar θ).comp f := by
  ext h
  rfl

theorem ker_le_ker_detChar (θ : Representation ℂ H V) : θ.ker ≤ (detChar θ).ker := by
  intro h hh
  apply Units.ext
  change LinearMap.det (θ h) = 1
  rw [MonoidHom.mem_ker.mp hh]
  exact map_one _

end Det

section Normalization

variable {H : Type uG} [Group H] (N : Subgroup H)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem detChar_twist_apply (χ : H →* ℂˣ) (θ : Representation ℂ H V) (h : H) :
    detChar (Langlands.twist χ θ) h = χ h ^ Module.finrank ℂ V * detChar θ h := by
  rw [detChar_twist, MonoidHom.mul_apply, MonoidHom.pow_apply]

/-- If the dimension is a power of the prime `p`, the determinant has finite order and its
restriction to `N` has `p`-power order, then the twist by some character trivial on `N` and on
the kernel of the representation has determinant of `p`-power order. -/
theorem exists_twist_detChar_pPower {p a : ℕ} (hp : p.Prime) (θ : Representation ℂ H V)
    (hdim : Module.finrank ℂ V = p ^ a) (hfin : ∃ n : ℕ, 0 < n ∧ ∀ h : H, detChar θ h ^ n = 1)
    (hN : ∃ b : ℕ, ∀ y : N, detChar θ y ^ (p ^ b) = 1) :
    ∃ γ : H →* ℂˣ, N ≤ γ.ker ∧ θ.ker ≤ γ.ker ∧
      ∃ s : ℕ, ∀ h : H, detChar (Langlands.twist γ θ) h ^ (p ^ s) = 1 := by
  obtain ⟨n, hn0, hn⟩ := hfin
  obtain ⟨b, hb⟩ := hN
  obtain ⟨s, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' p hp.ne_one
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  set δ := detChar θ with hδ
  obtain ⟨a', b', hab⟩ := Nat.Coprime.isCoprime (Nat.Coprime.pow_left s hcop)
  obtain ⟨x', y', hxy⟩ := Nat.Coprime.isCoprime (Nat.Coprime.pow_left a hcop)
  have hnz : ∀ h : H, δ h ^ (((p ^ s * m : ℕ)) : ℤ) = 1 := fun h => by
    rw [zpow_natCast, hn h]
  have hvm : ∀ h : H, (δ h ^ (a' * ((p ^ s : ℕ) : ℤ))) ^ m = 1 := by
    intro h
    rw [← zpow_natCast, ← zpow_mul,
      show a' * ((p ^ s : ℕ) : ℤ) * (m : ℤ) = ((p ^ s * m : ℕ) : ℤ) * a' by push_cast; ring,
      zpow_mul, hnz, one_zpow]
  have hvN : ∀ y : N, δ y ^ (a' * ((p ^ s : ℕ) : ℤ)) = 1 := by
    intro y
    apply eq_one_of_pow_coprime (Nat.Coprime.pow_left b hcop).symm (hvm y)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb y, one_zpow]
  let γ : H →* ℂˣ :=
    { toFun := fun h => (δ h ^ ((a' * ((p ^ s : ℕ) : ℤ)) * x'))⁻¹
      map_one' := by simp
      map_mul' := fun h k => by
        rw [map_mul, mul_zpow, mul_inv] }
  refine ⟨γ, ?_, ?_, s, ?_⟩
  · intro y hy
    change (δ y ^ ((a' * ((p ^ s : ℕ) : ℤ)) * x'))⁻¹ = 1
    rw [zpow_mul, hvN ⟨y, hy⟩, one_zpow, inv_one]
  · intro y hy
    have h1 : δ y = 1 := ker_le_ker_detChar θ hy
    change (δ y ^ ((a' * ((p ^ s : ℕ) : ℤ)) * x'))⁻¹ = 1
    rw [h1, one_zpow, inv_one]
  · intro h
    rw [detChar_twist_apply, hdim]
    change ((δ h ^ ((a' * ((p ^ s : ℕ) : ℤ)) * x'))⁻¹ ^ p ^ a * δ h) ^ p ^ s = 1
    have hexp : ((1 : ℤ) - (a' * ((p ^ s : ℕ) : ℤ)) * x' * ((p ^ a : ℕ) : ℤ)) *
        ((p ^ s : ℕ) : ℤ) = ((p ^ s * m : ℕ) : ℤ) * (b' + a' * ((p ^ s : ℕ) : ℤ) * y') := by
      push_cast at hab hxy ⊢
      linear_combination (-((p : ℤ) ^ s)) * hab + (-(a' * ((p : ℤ) ^ s) ^ 2)) * hxy
    have hE : ((δ h ^ ((a' * ((p ^ s : ℕ) : ℤ)) * x'))⁻¹ ^ p ^ a * δ h) ^ p ^ s =
        (δ h ^ (((p ^ s * m : ℕ)) : ℤ)) ^ (b' + a' * ((p ^ s : ℕ) : ℤ) * y') := by
      rw [← zpow_mul, ← hexp]
      have h1 : ((δ h ^ ((a' * ((p ^ s : ℕ) : ℤ)) * x'))⁻¹ ^ p ^ a * δ h) ^ p ^ s =
          ((δ h ^ ((a' * ((p ^ s : ℕ) : ℤ)) * x'))⁻¹ ^ ((p ^ a : ℕ) : ℤ) * δ h) ^ ((p ^ s : ℕ) : ℤ) := by
        rw [zpow_natCast, zpow_natCast]
      rw [h1]
      group
    rw [hE, hnz, one_zpow]

/-- A character killed by an exponent prime to `p` that twists one representation with
determinant of `p`-power order into another such representation is trivial, when the dimension
is a power of `p`. -/
theorem eq_one_of_detChar_pPower {p a : ℕ} {θ : Representation ℂ H V}
    (hdim : Module.finrank ℂ V = p ^ a) {χ : H →* ℂˣ} {m : ℕ} (hm : Nat.Coprime m p)
    (hχm : ∀ h : H, χ h ^ m = 1) {s t : ℕ} (h1 : ∀ h : H, detChar θ h ^ (p ^ s) = 1)
    (h2 : ∀ h : H, detChar (Langlands.twist χ θ) h ^ (p ^ t) = 1) : χ = 1 := by
  ext1 h
  refine eq_one_of_pow_coprime (Nat.Coprime.pow_right (a + t + s) hm).symm ?_ (hχm h)
  have h3 := h2 h
  rw [detChar_twist_apply, hdim, mul_pow, ← pow_mul] at h3
  have h4 : χ h ^ (p ^ a * p ^ t) = (detChar θ h ^ p ^ t)⁻¹ := eq_inv_of_mul_eq_one_left h3
  rw [pow_add, pow_add, pow_mul, h4, inv_pow, ← pow_mul, mul_comm, pow_mul, h1 h, one_pow,
    inv_one]

end Normalization

end Langlands.Clifford
