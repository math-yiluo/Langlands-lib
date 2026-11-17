import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.RingTheory.Int.Basic

/-! # Local lattices from positive functions satisfying the cube identity

A rational-valued function `q` on an abelian group `M` satisfying the cube
identity `q(x+y+z) + q(x) + q(y) + q(z) = q(x+y) + q(x+z) + q(y+z)` has a
biadditive symmetric polar form `polar q x y = q(x+y) - q(x) - q(y)`. If the
values of `q` have bounded denominators and `q` is positive away from zero,
then the preimage in `M` of every finitely generated rational subspace of
`ℚ ⊗[ℤ] M` is a finitely generated integer module. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Algebra.CubeQuadratic

variable {M : Type*} [AddCommGroup M]

/-- The cube identity (vanishing third difference) for a rational-valued
function on an abelian group. -/
def CubeIdentity (q : M → ℚ) : Prop :=
  ∀ x y z : M, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)

/-- The polar form of a rational-valued function. -/
def polar (q : M → ℚ) (x y : M) : ℚ := q (x + y) - q x - q y

theorem polar_comm (q : M → ℚ) (x y : M) : polar q x y = polar q y x := by
  simp only [polar, add_comm x y]
  ring

section Cube

variable {q : M → ℚ} (hq : CubeIdentity q)
include hq

/-- The cube identity forces the value at zero to vanish. -/
theorem map_zero_of_cubeIdentity : q 0 = 0 := by
  have h := hq 0 0 0
  simp only [add_zero] at h
  linarith

/-- The polar form of a function satisfying the cube identity is additive in
its first argument. -/
theorem polar_add_left (x y z : M) : polar q (x + y) z = polar q x z + polar q y z := by
  have h := hq x y z
  simp only [polar]
  linarith

/-- The polar form in its first argument, as an additive map. -/
def polarLeft (z : M) : M →+ ℚ :=
  AddMonoidHom.mk' (fun x => polar q x z) (fun x y => polar_add_left hq x y z)

theorem polar_zsmul_left (n : ℤ) (x z : M) : polar q (n • x) z = n * polar q x z := by
  have h := map_zsmul (polarLeft hq z) n x
  simpa only [polarLeft, AddMonoidHom.mk'_apply, zsmul_eq_mul] using h

theorem polar_neg_left (x z : M) : polar q (-x) z = -polar q x z := by
  have h := map_neg (polarLeft hq z) x
  simpa only [polarLeft, AddMonoidHom.mk'_apply] using h

/-- The diagonal of the polar form is the symmetrization of `q`. -/
theorem polar_self (x : M) : polar q x x = q x + q (-x) := by
  have h1 : polar q x (-x) = -polar q x x := by
    rw [polar_comm, polar_neg_left hq]
  have h0 := map_zero_of_cubeIdentity hq
  simp only [polar, add_neg_cancel] at h1 ⊢
  linarith

/-- A positive function satisfying the cube identity has positive-definite polar form. -/
theorem polar_self_pos (hpos : ∀ x : M, x ≠ 0 → 0 < q x) {x : M} (hx : x ≠ 0) :
    0 < polar q x x := by
  rw [polar_self hq]
  have h1 := hpos x hx
  have h2 := hpos (-x) (neg_ne_zero.mpr hx)
  linarith

omit hq in
/-- Bounded denominators of `q` give bounded denominators of its polar form. -/
theorem exists_int_polar {N : ℕ} (hN : ∀ x : M, ∃ z : ℤ, (N : ℚ) * q x = z) (x y : M) :
    ∃ z : ℤ, (N : ℚ) * polar q x y = z := by
  obtain ⟨a, ha⟩ := hN (x + y)
  obtain ⟨b, hb⟩ := hN x
  obtain ⟨c, hc⟩ := hN y
  refine ⟨a - b - c, ?_⟩
  simp only [polar, Int.cast_sub]
  rw [← ha, ← hb, ← hc]
  ring

end Cube

/-- **Local finite generation from a positive cube-identity function.**
Let `q : M → ℚ` satisfy the cube identity, have values in `N⁻¹ ℤ` for some
positive `N`, and be positive at every nonzero element. Then the preimage in
`M` of any finitely generated rational subspace of `ℚ ⊗[ℤ] M` is a finitely
generated integer module. -/
theorem fg_comap_of_cubeIdentity (q : M → ℚ) (hq : CubeIdentity q)
    (N : ℕ) (hN0 : 0 < N) (hN : ∀ x : M, ∃ z : ℤ, (N : ℚ) * q x = z)
    (hpos : ∀ x : M, x ≠ 0 → 0 < q x)
    (V : Submodule ℚ (ℚ ⊗[ℤ] M)) (hV : V.FG) :
    ((V.restrictScalars ℤ).comap (TensorProduct.mk ℤ ℚ M 1)).FG := by
  classical
  let S := nonZeroDivisors ℤ
  let ι := TensorProduct.mk ℤ ℚ M 1
  have hloc : IsLocalizedModule S ι :=
    IsLocalization.tensorProduct_isLocalizedModule (S := S) (A := ℚ)
  obtain ⟨s, hs⟩ := hV
  -- integral lifts of the chosen rational generators
  have hsurj := fun w : ℚ ⊗[ℤ] M => IsLocalizedModule.surj S ι w
  choose p hp using hsurj
  let y : ↥s → M := fun w => (p w).1
  let Z : Submodule ℤ M := Submodule.span ℤ (Set.range y)
  -- integer-valued polar pairings
  let zpol : M → M → ℤ := fun x x' => ⌊(N : ℚ) * polar q x x'⌋
  have hzpol : ∀ x x', ((zpol x x' : ℤ) : ℚ) = (N : ℚ) * polar q x x' := by
    intro x x'
    obtain ⟨z, hz⟩ := exists_int_polar hN x x'
    simp only [zpol, hz, Int.floor_intCast]
  let Φadd : M →+ (↥s → ℤ) :=
    AddMonoidHom.mk' (fun x w => zpol x (y w)) (by
      intro a b
      funext w
      apply Int.cast_injective (α := ℚ)
      simp only [Pi.add_apply, Int.cast_add, hzpol, polar_add_left hq]
      ring)
  let Φ : M →ₗ[ℤ] (↥s → ℤ) := Φadd.toIntLinearMap
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
  -- every rational combination of generators is, up to a nonzero integer, integral in `Z`
  have hclaim : ∀ v ∈ V, ∃ n : ℤ, n ≠ 0 ∧ ∃ x ∈ Z, (n : ℚ) • v = ι x := by
    intro v hv
    rw [← hs] at hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
        refine ⟨((p w).2 : ℤ), nonZeroDivisors.coe_ne_zero _, y ⟨w, hw⟩,
          Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩, ?_⟩
        have h := hp w
        rw [Submonoid.smul_def, ← algebraMap_smul ℚ] at h
        simpa only [algebraMap_int_eq, eq_intCast] using h
    | zero => exact ⟨1, one_ne_zero, 0, Z.zero_mem, by simp⟩
    | add a b _ _ ha hb =>
        obtain ⟨n₁, hn₁, x₁, hx₁, h₁⟩ := ha
        obtain ⟨n₂, hn₂, x₂, hx₂, h₂⟩ := hb
        refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, n₂ • x₁ + n₁ • x₂,
          Z.add_mem (Z.smul_mem n₂ hx₁) (Z.smul_mem n₁ hx₂), ?_⟩
        rw [map_add, map_zsmul, map_zsmul, ← h₁, ← h₂, ← Int.cast_smul_eq_zsmul ℚ,
          ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, smul_add, Int.cast_mul,
          mul_comm (n₁ : ℚ) (n₂ : ℚ)]
    | smul c a _ ha =>
        obtain ⟨n, hn, x, hx, h⟩ := ha
        refine ⟨c.den * n, mul_ne_zero (by exact_mod_cast c.den_nz) hn, c.num • x,
          Z.smul_mem c.num hx, ?_⟩
        rw [map_zsmul, ← h, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, Int.cast_mul,
          Int.cast_natCast, mul_assoc, mul_comm (n : ℚ) c, ← mul_assoc, Rat.den_mul_eq_num]
  -- the kernel of `Φ` meets the preimage trivially
  have hinj : ∀ m ∈ (V.restrictScalars ℤ).comap ι, Φ m = 0 → m = 0 := by
    intro m hm hΦ
    have hm' : ι m ∈ V := hm
    have hgen : ∀ w : ↥s, polar q (y w) m = 0 := by
      intro w
      have h := congrFun hΦ w
      have hc : ((zpol m (y w) : ℤ) : ℚ) = 0 := by
        change ((Φadd m w : ℤ) : ℚ) = 0
        rw [show Φadd m w = 0 from h, Int.cast_zero]
      rw [hzpol] at hc
      rw [polar_comm]
      exact (mul_eq_zero.mp hc).resolve_left hNq
    have hZ : ∀ x ∈ Z, polar q x m = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem a ha =>
          obtain ⟨w, rfl⟩ := ha
          exact hgen w
      | zero =>
          have := map_zero (polarLeft hq m)
          simpa only [polarLeft, AddMonoidHom.mk'_apply] using this
      | add a b _ _ ha hb => rw [polar_add_left hq, ha, hb, add_zero]
      | smul n a _ ha =>
          change polar q (n • a) m = 0
          rw [polar_zsmul_left hq, ha, mul_zero]
    obtain ⟨n, hn, x, hx, h⟩ := hclaim (ι m) hm'
    have hker : ι (n • m - x) = 0 := by
      rw [map_sub, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, h, sub_self]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S ι).mp hker
    rw [Submonoid.smul_def] at ht
    have ht' : ((t : ℤ) * n) • m = (t : ℤ) • x := by
      rw [mul_smul, ← sub_eq_zero, ← smul_sub]
      exact ht
    have hpol : ((t : ℤ) * n : ℤ) * polar q m m = 0 := by
      rw [← polar_zsmul_left hq, ht', polar_zsmul_left hq, hZ x hx, mul_zero]
    have htn : (((t : ℤ) * n : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast mul_ne_zero (nonZeroDivisors.coe_ne_zero t) hn
    have hzero : polar q m m = 0 := (mul_eq_zero.mp hpol).resolve_left htn
    by_contra hm0
    exact (polar_self_pos hq hpos hm0).ne' hzero
  apply Submodule.fg_of_fg_map_of_fg_inf_ker Φ
  · exact IsNoetherian.noetherian _
  · have hbot : (V.restrictScalars ℤ).comap ι ⊓ LinearMap.ker Φ = ⊥ := by
      rw [eq_bot_iff]
      rintro m ⟨hm, hk⟩
      exact (Submodule.mem_bot ℤ).mpr (hinj m hm hk)
    exact (congrArg Submodule.FG hbot).mpr Submodule.fg_bot

end Langlands.Algebra.CubeQuadratic
