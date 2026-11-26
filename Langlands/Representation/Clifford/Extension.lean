import Langlands.Representation.Clifford.Twist

/-!
# Extension of an invariant irreducible representation across a finite cyclic quotient
-/

noncomputable section

namespace Langlands.Clifford

open Representation

universe uG uV

section CyclicExtension

variable {H : Type uG} [Group H] (K : Subgroup H) [K.Normal] (g : H)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Conjugation by an integer power of `g`, as an endomorphism of the normal subgroup. -/
def conjPow (i : ℤ) : K →* K where
  toFun k := ⟨g ^ i * k * (g ^ i)⁻¹, Subgroup.Normal.conj_mem ‹K.Normal› k k.2 (g ^ i)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

@[simp] theorem coe_conjPow (i : ℤ) (k : K) :
    ((conjPow K g i k : K) : H) = g ^ i * k * (g ^ i)⁻¹ := rfl

variable {K g} (c : Representation ℂ K V)

/-- An invertible operator intertwining `c` with its conjugate by `g` conjugates by every
integer power of `g`. -/
theorem units_zpow_mul_eq (T : (Module.End ℂ V)ˣ)
    (hT : ∀ k : K, (T : Module.End ℂ V) * c k = c (conjPow K g 1 k) * T) (i : ℤ) (k : K) :
    ((T ^ i : (Module.End ℂ V)ˣ) : Module.End ℂ V) * c k =
      c (conjPow K g i k) * ((T ^ i : (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
  have hT' : ∀ k : K, ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) * c k =
      c (conjPow K g (-1) k) * ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
    intro k
    have h := hT (conjPow K g (-1) k)
    have hk : conjPow K g 1 (conjPow K g (-1) k) = k := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [hk] at h
    have h2 := congrArg (fun X => ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) * X *
      ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V)) h
    simp only [← mul_assoc, Units.inv_mul, one_mul] at h2
    rw [mul_assoc, Units.mul_inv, mul_one] at h2
    exact h2.symm
  induction i using Int.induction_on generalizing k with
  | zero =>
    simp only [zpow_zero, Units.val_one, one_mul, mul_one]
    congr 1
    apply Subtype.ext
    simp
  | succ i ih =>
    rw [zpow_add_one, Units.val_mul, mul_assoc, hT, ← mul_assoc, ih, mul_assoc]
    congr 2
    apply Subtype.ext
    simp [zpow_add_one, mul_assoc]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, mul_assoc, hT', ← mul_assoc, ih, mul_assoc]
    congr 2
    apply Subtype.ext
    simp [zpow_sub_one, mul_assoc]

variable [FiniteDimensional ℂ V]

/-- A normalized intertwiner: if `c` is irreducible and finite-dimensional and equivalent to its
conjugate by `g`, and `g ^ e ∈ K` with `e > 0`, there is an invertible operator `T` intertwining `c` with its conjugate by
`g` and with `T ^ e = c (g ^ e)`. -/
theorem exists_normalized_intertwiner (hc : c.IsIrreducible) {e : ℕ} (he : 0 < e)
    (hge : g ^ e ∈ K) (hinv : Nonempty (Representation.Equiv (c.comp (conjPow K g 1)) c)) :
    ∃ T : (Module.End ℂ V)ˣ, (∀ k : K, (T : Module.End ℂ V) * c k = c (conjPow K g 1 k) * T) ∧
      T ^ e = c.asGroupHom ⟨g ^ e, hge⟩ := by
  obtain ⟨E⟩ := hinv
  let T₀ : (Module.End ℂ V)ˣ :=
    ⟨E.symm.toLinearMap, E.toLinearMap, by ext v; simp, by ext v; simp⟩
  have hT₀ : ∀ k : K, (T₀ : Module.End ℂ V) * c k = c (conjPow K g 1 k) * T₀ := by
    intro k
    apply LinearMap.ext
    intro v
    change E.symm (c k v) = c (conjPow K g 1 k) (E.symm v)
    apply E.toLinearEquiv.injective
    have h := LinearMap.congr_fun (E.isIntertwining' k) (E.symm v)
    change E (c (conjPow K g 1 k) (E.symm v)) = c k (E (E.symm v)) at h
    change E (E.symm (c k v)) = E (c (conjPow K g 1 k) (E.symm v))
    rw [h]
    simp
  let gE : K := ⟨g ^ e, hge⟩
  let S : Module.End ℂ V := c gE⁻¹ * ((T₀ ^ e : (Module.End ℂ V)ˣ) : Module.End ℂ V)
  have hS : ∀ k : K, S * c k = c k * S := by
    intro k
    have h1 := units_zpow_mul_eq c T₀ hT₀ (e : ℤ) k
    rw [zpow_natCast] at h1
    have h2 : c (conjPow K g (e : ℤ) k) = c gE * c k * c gE⁻¹ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [gE, zpow_natCast]
    change c gE⁻¹ * ((T₀ ^ e : (Module.End ℂ V)ˣ) : Module.End ℂ V) * c k =
      c k * (c gE⁻¹ * ((T₀ ^ e : (Module.End ℂ V)ˣ) : Module.End ℂ V))
    rw [mul_assoc, h1, h2, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel,
      map_one, one_mul, mul_assoc]
  let Sint : IntertwiningMap c c := ⟨S, fun k => hS k⟩
  obtain ⟨l, hl⟩ := CyclicRestriction.end_eq_smul_one c hc Sint
  have hSl : S = l • 1 := hl
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ K) c.asModule
  have hSu : IsUnit S := by
    have h1 : IsUnit (c gE⁻¹) := (c.asGroupHom gE⁻¹).isUnit
    exact h1.mul (Units.isUnit _)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [hSl, zero_smul] at hSu
    exact not_isUnit_zero hSu
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq l he
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow he.ne'] at hμ
    exact hl0 hμ.symm
  let T : (Module.End ℂ V)ˣ :=
    ⟨μ⁻¹ • (T₀ : Module.End ℂ V), μ • ((T₀⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V),
      by rw [smul_mul_smul_comm, inv_mul_cancel₀ hμ0, Units.mul_inv, one_smul],
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hμ0, Units.inv_mul, one_smul]⟩
  refine ⟨T, ?_, ?_⟩
  · intro k
    change μ⁻¹ • (T₀ : Module.End ℂ V) * c k = c (conjPow K g 1 k) * (μ⁻¹ • (T₀ : Module.End ℂ V))
    rw [smul_mul_assoc, hT₀, mul_smul_comm]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    change (μ⁻¹ • (T₀ : Module.End ℂ V)) ^ e = c gE
    have hTe : ((T₀ ^ e : (Module.End ℂ V)ˣ) : Module.End ℂ V) = c gE * S := by
      change _ = c gE * (c gE⁻¹ * _)
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [smul_pow, ← Units.val_pow_eq_pow_val, hTe, hSl, mul_smul_comm, mul_one, smul_smul,
      inv_pow, hμ, inv_mul_cancel₀ hl0, one_smul]

/-- An irreducible finite-dimensional representation of a normal subgroup `K`, equivalent to
its conjugate by `g`, extends to `H` when every element of `H` is a power of `g`
modulo `K` and the powers of `g` lying in `K` are exactly the multiples of `e > 0`. -/
theorem exists_extension (hc : c.IsIrreducible) {e : ℕ} (he : 0 < e)
    (hord : ∀ i : ℤ, g ^ i ∈ K → (e : ℤ) ∣ i) (hge : g ^ e ∈ K)
    (hgen : ∀ x : H, ∃ i : ℤ, x * (g ^ i)⁻¹ ∈ K)
    (hinv : Nonempty (Representation.Equiv (c.comp (conjPow K g 1)) c)) :
    ∃ θ : Representation ℂ H V, θ.comp K.subtype = c := by
  classical
  obtain ⟨T, hT, hTe⟩ := exists_normalized_intertwiner c hc he hge hinv
  have hTpow : ∀ (i : ℤ) (hi : g ^ i ∈ K),
      ((T ^ i : (Module.End ℂ V)ˣ) : Module.End ℂ V) = c ⟨g ^ i, hi⟩ := by
    intro i hi
    obtain ⟨t, rfl⟩ := hord i hi
    rw [zpow_mul, zpow_natCast, hTe, ← map_zpow]
    change c (⟨g ^ e, hge⟩ ^ t) = _
    congr 1
    apply Subtype.ext
    simp [zpow_mul, zpow_natCast]
  let idx : H → ℤ := fun x => Classical.choose (hgen x)
  have hidx : ∀ x, x * (g ^ idx x)⁻¹ ∈ K := fun x => Classical.choose_spec (hgen x)
  let θf : H → Module.End ℂ V := fun x =>
    c ⟨x * (g ^ idx x)⁻¹, hidx x⟩ * ((T ^ idx x : (Module.End ℂ V)ˣ) : Module.End ℂ V)
  have hwd : ∀ (x : H) (i : ℤ) (hi : x * (g ^ i)⁻¹ ∈ K),
      θf x = c ⟨x * (g ^ i)⁻¹, hi⟩ * ((T ^ i : (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
    intro x i hi
    have hk : g ^ (idx x - i) ∈ K := by
      have h := K.mul_mem (K.inv_mem (hidx x)) hi
      convert h using 1
      group
    have hsplit : (⟨x * (g ^ idx x)⁻¹, hidx x⟩ : K) =
        ⟨x * (g ^ i)⁻¹, hi⟩ * (⟨g ^ (idx x - i), hk⟩ : K)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    change c ⟨x * (g ^ idx x)⁻¹, hidx x⟩ * ((T ^ idx x : (Module.End ℂ V)ˣ) : Module.End ℂ V) = _
    have hT' : T ^ idx x = T ^ (idx x - i) * T ^ i := by
      rw [← zpow_add]
      congr 1
      ring
    rw [hsplit, hT', Units.val_mul, hTpow _ hk,
      map_mul, mul_assoc, ← mul_assoc (c _⁻¹), ← map_mul, inv_mul_cancel, map_one, one_mul]
  let θ : Representation ℂ H V :=
    { toFun := θf
      map_one' := by
        rw [hwd 1 0 (by simp)]
        simp only [zpow_zero, inv_one, mul_one, Units.val_one]
        exact map_one c
      map_mul' := fun x y => by
        have hxy : x * y * (g ^ (idx x + idx y))⁻¹ ∈ K := by
          have h := K.mul_mem (hidx x) (conjPow K g (idx x) ⟨_, hidx y⟩).2
          convert h using 1
          simp only [coe_conjPow]
          group
        rw [hwd (x * y) _ hxy]
        have hsplit : (⟨x * y * (g ^ (idx x + idx y))⁻¹, hxy⟩ : K) =
            ⟨x * (g ^ idx x)⁻¹, hidx x⟩ * conjPow K g (idx x) ⟨_, hidx y⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, coe_conjPow]
          group
        rw [hsplit, map_mul, zpow_add, Units.val_mul]
        simp only [mul_assoc]
        rw [← mul_assoc (c (conjPow K g (idx x) _)), ← units_zpow_mul_eq c T hT]
        simp only [θf, mul_assoc] }
  refine ⟨θ, ?_⟩
  ext k v
  change θf k v = c k v
  rw [hwd k 0 (by simp)]
  simp

end CyclicExtension

end Langlands.Clifford
