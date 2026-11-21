import Langlands.GroupScheme.Quaternionic.KneserThreeQuaternion
import Langlands.GroupScheme.Quaternionic.AntihermitianForm

/-! # The symmetric component of a quaternionic skew-hermitian form -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  (Q : QuatData F D)

local notation "E" => field Q.c
local notation "κ" => SU3Root.conjugation F E

/-- Right multiplication by an embedded field element multiplies the second coordinate. -/
theorem snd_mul_ι (z : D) (a : E) : Q.snd (z * Q.ι a) = Q.snd z * a := by
  conv_lhs => rw [← Q.decompose z, add_mul, mul_assoc, ← map_mul, ← map_mul]
  exact Q.snd_mk _ _

/-- Left multiplication by an embedded field element multiplies the second coordinate
  by its nontrivial conjugate. -/
theorem snd_ι_mul (a : E) (z : D) : Q.snd (Q.ι a * z) = κ a * Q.snd z := by
  have h : Q.ι a * Q.j = Q.j * Q.ι (κ a) := by
    have h := Q.j_mul_ι (κ a)
    rw [SU3Root.conjugation_involutive] at h
    exact h.symm
  conv_lhs => rw [← Q.decompose z, mul_add, ← mul_assoc (Q.ι a), h, mul_assoc,
    ← map_mul, ← map_mul]
  exact Q.snd_mk _ _

@[simp] theorem snd_bar (z : D) : Q.snd (Q.bar z) = -Q.snd z := by
  unfold bar
  rw [map_sub, snd_ι, snd_j_mul, zero_sub]

@[simp] theorem fst_bar (z : D) : Q.fst (Q.bar z) = κ (Q.fst z) := by
  unfold bar
  rw [map_sub, fst_ι, fst_j_mul, sub_zero]

@[simp] theorem bar_ι (a : E) : Q.bar (Q.ι a) = Q.ι (κ a) := by
  rw [bar, fst_ι, snd_ι, map_zero, mul_zero, sub_zero]

/-- On the pure subspace, the second coordinate vanishes exactly on the line
  of the chosen quadratic root. -/
theorem snd_eq_zero_iff_mem_pureLine (h2 : (2 : F) ≠ 0) {z : D} (hz : Q.bar z = -z) :
    Q.snd z = 0 ↔ ∃ b : F, z = b • Q.x := by
  constructor
  · intro hs
    have hfst := congrArg Q.fst hz
    rw [Q.fst_bar, map_neg] at hfst
    obtain ⟨a, b, hab⟩ := QuadField.exists_eq (Q.fst z)
    have ha : a = 0 := by
      have ht : ((2 : F) * a) • (1 : E) = 0 := by
        calc
          _ = κ (Q.fst z) + Q.fst z := by
            rw [hab, map_add, map_smul, map_smul, map_one, QuadField.conjugation_root,
              mul_smul, two_smul, smul_neg]
            abel
          _ = 0 := by rw [hfst, neg_add_cancel]
      exact (mul_eq_zero.mp ((smul_eq_zero.mp ht).resolve_right one_ne_zero)).resolve_left h2
    refine ⟨b, (Q.decompose z).symm.trans ?_⟩
    rw [hs, map_zero, mul_zero, add_zero, hab, ha, zero_smul, zero_add, map_smul, Q.ι_root]
  · rintro ⟨b, rfl⟩
    rw [map_smul, ← Q.ι_root, Q.snd_ι, smul_zero]

section Form

variable {τ : FirstKindInvolution F D} {V : Type v} [AddCommGroup V]
  [Module D V] [Module F V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V) (hbar : ∀ z, τ z = Q.bar z)

/-- The component of a skew-hermitian form along the second quaternionic basis
  direction is symmetric bilinear over the embedded quadratic field. -/
def symmetricComponent :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    LinearMap.BilinForm E V := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  refine LinearMap.mk₂ E (fun x y => κ (Q.snd (B x y))) ?_ ?_ ?_ ?_
  · intro x x' y
    rw [B.add_left, map_add, map_add]
  · intro a x y
    change κ (Q.snd (B (Q.ι a • x) y)) = a * κ (Q.snd (B x y))
    rw [B.smul_left, Q.snd_ι_mul, map_mul, SU3Root.conjugation_involutive]
  · intro x y y'
    rw [B.add_right, map_add, map_add]
  · intro a x y
    change κ (Q.snd (B x (Q.ι a • y))) = a * κ (Q.snd (B x y))
    rw [B.smul_right, hbar, Q.bar_ι, Q.snd_mul_ι, map_mul, SU3Root.conjugation_involutive, mul_comm]

@[simp] theorem symmetricComponent_apply (x y : V) :
    Q.symmetricComponent B hbar x y = κ (Q.snd (B x y)) := rfl

/-- The component has the same value on a pair in either order. -/
theorem symmetricComponent_swap (x y : V) :
    Q.symmetricComponent B hbar y x = Q.symmetricComponent B hbar x y := by
  simp only [symmetricComponent_apply, B.skew x y, map_neg, hbar, Q.snd_bar, neg_neg]

/-- A nondegenerate quaternionic pairing has a nondegenerate symmetric component. -/
theorem symmetricComponent_nondegenerate (hB : B.toBilin.SeparatingLeft) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    (Q.symmetricComponent B hbar).Nondegenerate := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  have hs : (Q.symmetricComponent B hbar).IsSymm :=
    ⟨fun x y => Q.symmetricComponent_swap B hbar y x⟩
  apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  apply hB x
  intro y
  change B x y = 0
  by_contra hxy
  have h := hx (τ ((B x y)⁻¹ * Q.j) • y)
  have hj : Q.snd Q.j = 1 := by simpa only [map_one, mul_one] using Q.snd_j_mul 1
  rw [symmetricComponent_apply, B.smul_right, τ.apply_apply, ← mul_assoc,
    mul_inv_cancel₀ hxy, one_mul, hj, map_one] at h
  exact one_ne_zero h

/-- The quadratic values of the component vanish exactly when the original
  skew-hermitian value is a scalar multiple of the chosen pure quaternion. -/
theorem symmetricComponent_self_eq_zero_iff (h2 : (2 : F) ≠ 0) (x : V) :
    Q.symmetricComponent B hbar x x = 0 ↔ ∃ b : F, B x x = b • Q.x := by
  have hx : Q.bar (B x x) = -(B x x) := by
    rw [← hbar, ← neg_neg (τ (B x x)), ← B.skew x x]
  rw [symmetricComponent_apply, map_eq_zero_iff κ (κ).injective]
  exact Q.snd_eq_zero_iff_mem_pureLine h2 hx

end Form

end Langlands.GroupScheme.KneserThree.QuatData

namespace Langlands.GroupScheme.KneserThree.Quaternion

open Quaternionic

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

/-- The quaternion basis construction can be prescribed at any nonzero pure quaternion. -/
theorem exists_quatData_of_pure (h2 : (2 : F) ≠ 0) {x : D}
    (hx₀ : x ≠ 0) (hx : conj σ hdim hsym x = -x) :
    ∃ Q : QuatData F D, Q.x = x ∧ ∀ z, conj σ hdim hsym z = Q.bar z := by
  let l : D := ell σ hdim hsym
  let μ := -(x * l)
  have hl : l ≠ 0 := (ell σ hdim hsym).ne_zero
  have hrel := congrArg (fun a : D => a * l) hx
  change (l * σ x * l⁻¹) * l = -x * l at hrel
  rw [mul_assoc (l * σ x), inv_mul_cancel₀ hl, mul_one, neg_mul] at hrel
  have hμ : σ μ = μ := by
    change σ (-(x * l)) = -(x * l)
    rw [FirstKindInvolution.map_neg, FirstKindInvolution.map_mul,
      show σ l = -l from sigma_ell σ hdim hsym, neg_mul, neg_neg]
    exact hrel
  have hμ₀ : μ ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hx₀ hl)
  refine ⟨quatData σ hdim hsym h2 hμ hμ₀, ?_, conj_eq_bar σ hdim hsym h2 hμ hμ₀⟩
  change -(-(x * l) * l⁻¹) = x
  rw [neg_mul, neg_neg, mul_assoc, mul_inv_cancel₀ hl, mul_one]

end Langlands.GroupScheme.KneserThree.Quaternion
