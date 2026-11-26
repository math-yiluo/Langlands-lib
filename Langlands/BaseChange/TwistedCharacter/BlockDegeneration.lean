import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Tactic.NoncommRing

/-! # Diagonal blocks in conjugacy-orbit closures -/

noncomputable section

namespace Langlands.BaseChange

open Filter Set
open scoped Topology

section Blocks

variable {R : Type*} [Ring R]

/-- The upper triangular block subalgebra for a projection `p`. -/
def upperBlockAlgebra (F : Type*) [CommRing F] [Algebra F R]
    (p : R) (hp : IsIdempotentElem p) : Subalgebra F R where
  carrier := {a | (1 - p) * a * p = 0}
  zero_mem' := by simp
  one_mem' := by
    change (1 - p) * 1 * p = 0
    simpa only [mul_one] using hp.one_sub_mul_self
  add_mem' {a b} ha hb := by
    change (1 - p) * (a + b) * p = 0
    rw [mul_add, add_mul, ha, hb, add_zero]
  mul_mem' {a b} ha hb := by
    let q := 1 - p
    have h₁ : p + q = 1 := by simp [q]
    change q * a * p = 0 at ha
    change q * b * p = 0 at hb
    change q * (a * b) * p = 0
    have hsplit : q * (a * b) * p = q * a * (p + q) * b * p := by rw [h₁, mul_one]; noncomm_ring
    rw [hsplit, show q * a * (p + q) * b * p = (q * a * p) * b * p + q * a * (q * b * p) by
      noncomm_ring, ha, hb, zero_mul, zero_mul, mul_zero, add_zero]
  algebraMap_mem' t := by
    change (1 - p) * algebraMap F R t * p = 0
    rw [Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm, mul_one,
      Algebra.smul_mul_assoc, hp.one_sub_mul_self, smul_zero]

/-- Discard the off-diagonal block. This is multiplicative on the upper triangular algebra. -/
def diagonalBlockHom (F : Type*) [CommRing F] [Algebra F R]
    (p : R) (hp : IsIdempotentElem p) : upperBlockAlgebra F p hp →ₐ[F] R := by
  let q := 1 - p
  have h₁ : p + q = 1 := by simp [q]
  have hq : IsIdempotentElem q := hp.one_sub
  have hpq : p * q = 0 := hp.mul_one_sub_self
  have hqp : q * p = 0 := hp.one_sub_mul_self
  refine
    { toFun := fun a => p * a.val * p + q * a.val * q
      map_zero' := by simp
      map_one' := by simpa only [Subalgebra.coe_one, mul_one, hp.eq, hq.eq] using h₁
      map_add' := fun a b => by simp only [Subalgebra.coe_add]; noncomm_ring
      map_mul' := ?_
      commutes' := ?_ }
  · intro a b
    have ha : q * a.val * p = 0 := a.prop
    have hb : q * b.val * p = 0 := b.prop
    change p * (a.val * b.val) * p + q * (a.val * b.val) * q =
      (p * a.val * p + q * a.val * q) * (p * b.val * p + q * b.val * q)
    have hleft : p * (a.val * b.val) * p = p * a.val * p * b.val * p := by
      calc
        _ = p * a.val * (p + q) * b.val * p := by rw [h₁, mul_one]; noncomm_ring
        _ = p * a.val * p * b.val * p + p * a.val * (q * b.val * p) := by noncomm_ring
        _ = _ := by rw [hb, mul_zero, add_zero]
    have hright : q * (a.val * b.val) * q = q * a.val * q * b.val * q := by
      calc
        _ = q * a.val * (p + q) * b.val * q := by rw [h₁, mul_one]; noncomm_ring
        _ = (q * a.val * p) * b.val * q + q * a.val * q * b.val * q := by noncomm_ring
        _ = _ := by rw [ha, zero_mul, zero_mul, zero_add]
    rw [hleft, hright]
    calc
      _ = p * a.val * (p * p) * b.val * p + q * a.val * (q * q) * b.val * q := by
        rw [hp.eq, hq.eq]
      _ = p * a.val * (p * p) * b.val * p + p * a.val * (p * q) * b.val * q +
          q * a.val * (q * p) * b.val * p + q * a.val * (q * q) * b.val * q := by
        simp [hpq, hqp]
      _ = _ := by noncomm_ring
  · intro t
    change p * algebraMap F R t * p + q * algebraMap F R t * q = _
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [Algebra.mul_smul_comm, mul_one, Algebra.smul_mul_assoc, hp.eq, hq.eq,
      ← smul_add, h₁]

end Blocks

section Closure

variable {F B R : Type*} [NontriviallyNormedField F] [Ring B] [Algebra F B]
  [Ring R] [Algebra F R] [TopologicalSpace R] [ContinuousAdd R] [ContinuousSMul F R]

private theorem exists_dilationUnit (p : B) (hp : IsIdempotentElem p) {t : F} (ht : t ≠ 0) :
    ∃ u : Bˣ, u.val = t • p + (1 - p) ∧ (u⁻¹ : Bˣ).val = t⁻¹ • p + (1 - p) := by
  let q := 1 - p
  have h₁ : p + q = 1 := by simp [q]
  have hq : IsIdempotentElem q := hp.one_sub
  have hpq : p * q = 0 := hp.mul_one_sub_self
  have hqp : q * p = 0 := hp.one_sub_mul_self
  have hmul {x y : F} (hxy : x * y = 1) : (x • p + q) * (y • p + q) = 1 := by
    simp [add_mul, mul_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul,
      hp.eq, hq.eq, hpq, hqp, (mul_comm y x).trans hxy, h₁]
  exact ⟨⟨t • p + q, t⁻¹ • p + q, hmul (mul_inv_cancel₀ ht), hmul (inv_mul_cancel₀ ht)⟩,
    rfl, rfl⟩

/-- The diagonal blocks of a triangular element belong to its orbit closure under
conjugation by units of an algebra containing the projection. -/
theorem diagonalBlock_mem_closure_conjugates (j : B →ₐ[F] R) (p : B)
    (hp : IsIdempotentElem p) (a : upperBlockAlgebra F (j p) (hp.map j)) :
    diagonalBlockHom F (j p) (hp.map j) a ∈
      closure (range fun g : Bˣ => j g.val * a.val * j (g⁻¹ : Bˣ).val) := by
  let P := j p
  let Q := 1 - P
  let d := diagonalBlockHom F P (hp.map j) a
  let b := P * a.val * Q
  have htri : Q * a.val * P = 0 := a.prop
  have hd : d = P * a.val * P + Q * a.val * Q := rfl
  have hlim : Tendsto (fun t : F => d + t • b) (𝓝[≠] (0 : F)) (𝓝 d) := by
    have hcont : Continuous (fun t : F => d + t • b) := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using
      (hcont.continuousAt (x := (0 : F))).tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  obtain ⟨u, hu, hv⟩ := exists_dilationUnit p hp ht'
  use u
  change j u.val * a.val * j (u⁻¹ : Bˣ).val = d + t • b
  rw [hu, hv, map_add, map_add, map_sub, map_one, map_smul, map_smul]
  change (t • P + Q) * a.val * (t⁻¹ • P + Q) = d + t • b
  rw [hd]
  simp only [mul_add, add_mul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, htri, b]
  rw [add_zero, smul_smul, inv_mul_cancel₀ ht', one_smul]
  abel

end Closure

end Langlands.BaseChange
