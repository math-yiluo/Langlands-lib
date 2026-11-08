import Langlands.GroupTheory.ExtensionAkizukiWitt
import Langlands.ClassFieldTheory.Local.CyclicClass

/-! # Power sections of cyclic quotients -/

noncomputable section

namespace Langlands.GroupExtensionPushout

open Langlands.ClassFieldTheory.Local

universe u v

variable {W : Type u} {G : Type v} [Group W] [Group G] {n : ℕ} [NeZero n]
  (q : W →* G) (χ : G ≃* Multiplicative (ZMod n)) (w : W)
  (hw : χ (q w) = Multiplicative.ofAdd 1)

omit [NeZero n] in
include hw in
/-- The coordinate of a power of the generator. -/
theorem cyclicCoordinate_pow (k : ℕ) :
    χ (q (w ^ k)) = Multiplicative.ofAdd (k : ZMod n) := by
  rw [map_pow, map_pow, hw, ← ofAdd_nsmul, nsmul_one]

/-- The normalized section sending the element of coordinate `k`, with
`0 ≤ k < n`, to `w ^ k`. -/
def powerSection : Section q where
  toFun g := w ^ (χ g).toAdd.val
  right_inv g := by
    apply χ.injective
    rw [cyclicCoordinate_pow q χ w hw, ZMod.natCast_zmod_val, ofAdd_toAdd]
  normalized := by
    simp

@[simp] theorem powerSection_apply (g : G) :
    powerSection q χ w hw g = w ^ (χ g).toAdd.val := rfl

/-- The `n`-th power of the generator, as an element of the kernel. -/
def powerKernel : q.ker :=
  ⟨w ^ n, by
    rw [MonoidHom.mem_ker]
    apply χ.injective
    rw [cyclicCoordinate_pow q χ w hw, ZMod.natCast_self, map_one]
    rfl⟩

omit [NeZero n] in
@[simp] theorem powerKernel_coe : (powerKernel q χ w hw : W) = w ^ n := rfl

omit [Group G] [NeZero n] in
/-- Division with remainder in the exponent of `w`. -/
theorem pow_eq_pow_div_mul_pow_mod (m : ℕ) :
    w ^ m = (w ^ n) ^ (m / n) * w ^ (m % n) := by
  rw [← pow_mul, ← pow_add, Nat.div_add_mod]

/-- The factor set of the power section is the carry power of `w ^ n`. -/
theorem factorKernel_powerSection (g h : G) :
    (powerSection q χ w hw).factorKernel g h =
      powerKernel q χ w hw ^ cyclicCarry (χ g).toAdd (χ h).toAdd := by
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, powerKernel_coe]
  change w ^ (χ g).toAdd.val * w ^ (χ h).toAdd.val * (w ^ (χ (g * h)).toAdd.val)⁻¹ =
    (w ^ n) ^ cyclicCarry (χ g).toAdd (χ h).toAdd
  rw [map_mul, toAdd_mul, ← pow_add, ← cyclicCarry_spec, pow_add, mul_inv_cancel_right,
    pow_mul]

variable {A : Type v} [CommGroup A] [MulDistribMulAction G A]

/-- The factor cocycle of the power section is the carry cocycle of `r (w ^ n)`. -/
theorem cocycle_powerSection (r : q.ker →* A)
    (hr : ∀ (x : W) (k : q.ker), r (conjugateKernel q x k) = q x • r k) (g h : G) :
    (powerSection q χ w hw).cocycle r hr (g, h) =
      r (powerKernel q χ w hw) ^ cyclicCarry (χ g).toAdd (χ h).toAdd := by
  change r ((powerSection q χ w hw).factorKernel g h) = _
  rw [factorKernel_powerSection, map_pow]

omit [NeZero n] in
/-- Exactly one standard representative modulo `n` reaches `n` after adding one. -/
theorem sum_val_add_one_div [NeZero n] :
    ∑ x : ZMod n, (x.val + 1) / n = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel NeZero.one_le).symm⟩
  change ∑ x : Fin (m + 1), ((x : ℕ) + 1) / (m + 1) = 1
  rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · simp
  · intro i _
    apply Nat.div_eq_of_lt
    simp only [Fin.val_castSucc]
    omega

include hw in
/-- The coset-product transfer of the generator, computed with the power section,
is the value at `w ^ n`. -/
theorem transfer_powerSection [Fintype G] {M : Type*} [CommGroup M] {K : Subgroup W}
    [K.FiniteIndex] (ϕ : K →* M) (hK : q.ker = K) (hmem : w ^ n ∈ K) :
    ϕ.transfer w = ϕ ⟨w ^ n, hmem⟩ := by
  rw [transfer_eq_prod_section ϕ q hK (powerSection q χ w hw)
    (powerSection q χ w hw).right_inv w]
  have hterm : ∀ (h : G) (hm),
      ϕ ⟨powerSection q χ w hw h * w * (powerSection q χ w hw (h * q w))⁻¹, hm⟩ =
        ϕ ⟨w ^ n, hmem⟩ ^ (((χ h).toAdd.val + 1) / n) := by
    intro h hm
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    change w ^ (χ h).toAdd.val * w * (w ^ (χ (h * q w)).toAdd.val)⁻¹ =
      (w ^ n) ^ (((χ h).toAdd.val + 1) / n)
    have hc : (χ (h * q w)).toAdd = (((χ h).toAdd.val + 1 : ℕ) : ZMod n) := by
      rw [map_mul, hw, toAdd_mul, toAdd_ofAdd, Nat.cast_add, ZMod.natCast_zmod_val,
        Nat.cast_one]
    rw [hc, ZMod.val_natCast, ← pow_succ,
      pow_eq_pow_div_mul_pow_mod w ((χ h).toAdd.val + 1), mul_inv_cancel_right]
  rw [Finset.prod_congr rfl (fun h _ => hterm h _), Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ h : G, ((χ h).toAdd.val + 1) / n = 1 :=
    (Fintype.sum_equiv (χ.toEquiv.trans Multiplicative.toAdd) _
      (fun x : ZMod n => (x.val + 1) / n) (fun _ => rfl)).trans sum_val_add_one_div
  rw [hsum, pow_one]

end Langlands.GroupExtensionPushout
