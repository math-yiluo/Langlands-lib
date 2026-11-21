import Langlands.GroupScheme.Quaternionic.SkewHermitianQuadraticComponent
import Mathlib.Tactic.Abel

/-! # Semilinear multiplication on a skew-hermitian symmetric component -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] (Q : QuatData F D)
  {V : Type v} [AddCommGroup V] [Module D V]

local notation "E" => field Q.c
local notation "κ" => SU3Root.conjugation F E
local notation "d" => algebraMap F E Q.δ

/-- Left multiplication by the second quaternion generator is semilinear over the
  embedded quadratic field. -/
def jAction :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    V →ₛₗ[(κ).toRingHom] V := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  refine { toFun := fun x => Q.j • x, map_add' := smul_add Q.j, map_smul' := ?_ }
  intro a x
  change Q.j • (Q.ι a • x) = Q.ι (κ a) • (Q.j • x)
  rw [smul_smul, smul_smul, Q.j_mul_ι]

@[simp] theorem jAction_apply (x : V) : Q.jAction x = Q.j • x := rfl

/-- The square of the semilinear action is the scalar square of the generator. -/
theorem jAction_sq (x : V) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    Q.jAction (Q.jAction x) = d • x := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  change Q.j • (Q.j • x) = Q.ι d • x
  rw [smul_smul, Q.j_mul_j, Q.ι.commutes]

private theorem j_ne_zero : Q.j ≠ 0 := by
  have h := Q.basis.ne_zero 2
  rwa [show Q.basis 2 = Q.j from congrFun Q.basis_eq 2] at h

private theorem scalar_j_sq_ne_zero : d ≠ 0 := by
  intro h
  have hδ : Q.δ = 0 := (algebraMap F E).injective (h.trans (map_zero _).symm)
  have hmul : Q.j * Q.j = 0 := by rw [Q.j_mul_j, hδ, map_zero]
  exact (mul_ne_zero Q.j_ne_zero Q.j_ne_zero) hmul

/-- Multiplication by the second generator is bijective, with inverse a scalar
  multiple of the same action. -/
theorem jAction_bijective : Function.Bijective (Q.jAction (V := V)) := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  have hd : d ≠ 0 := Q.scalar_j_sq_ne_zero
  constructor
  · intro x y h
    have he := congrArg (Q.jAction (V := V)) h
    rw [Q.jAction_sq, Q.jAction_sq] at he
    simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using congrArg (d⁻¹ • ·) he
  · intro x
    refine ⟨d⁻¹ • Q.jAction x, ?_⟩
    have hk : κ d⁻¹ = d⁻¹ := by rw [map_inv₀, AlgEquiv.commutes]
    rw [LinearMap.map_smulₛₗ]
    change κ (d⁻¹) • Q.jAction (Q.jAction x) = _
    rw [hk, Q.jAction_sq,
      smul_smul, inv_mul_cancel₀ hd, one_smul]

private theorem ι_mul_j (a : E) : Q.ι a * Q.j = Q.j * Q.ι (κ a) := by
  have h := Q.j_mul_ι (κ a)
  rw [SU3Root.conjugation_involutive] at h
  exact h.symm

private theorem snd_j_mul_any (z : D) : Q.snd (Q.j * z) = Q.fst z := by
  conv_lhs => rw [← Q.decompose z, mul_add, ← mul_assoc Q.j Q.j,
    Q.j_mul_j, ← Q.ι.commutes Q.δ, ← map_mul]
  rw [map_add, Q.snd_j_mul, Q.snd_ι, add_zero]

private theorem fst_j_mul_any (z : D) : Q.fst (Q.j * z) = d * Q.snd z := by
  conv_lhs => rw [← Q.decompose z, mul_add, ← mul_assoc Q.j Q.j,
    Q.j_mul_j, ← Q.ι.commutes Q.δ, ← map_mul]
  rw [map_add, Q.fst_j_mul, Q.fst_ι, zero_add]

private theorem snd_mul_j (z : D) : Q.snd (z * Q.j) = κ (Q.fst z) := by
  conv_lhs => rw [← Q.decompose z, add_mul, Q.ι_mul_j, mul_assoc Q.j,
    Q.ι_mul_j, ← mul_assoc Q.j Q.j, Q.j_mul_j, ← Q.ι.commutes Q.δ, ← map_mul]
  rw [map_add, Q.snd_j_mul, Q.snd_ι, add_zero]

private theorem bar_j : Q.bar Q.j = -Q.j := by
  have hf : Q.fst Q.j = 0 := by simpa only [map_one, mul_one] using Q.fst_j_mul 1
  have hs : Q.snd Q.j = 1 := by simpa only [map_one, mul_one] using Q.snd_j_mul 1
  rw [bar, hf, hs, map_zero, map_zero, map_one, mul_one, zero_sub]

variable {τ : FirstKindInvolution F D} [Module F V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V) (hbar : ∀ z, τ z = Q.bar z)

/-- Pairing with a translated first argument recovers the other quaternion coordinate. -/
theorem symmetricComponent_jAction_left (x y : V) :
    Q.symmetricComponent B hbar (Q.jAction x) y = κ (Q.fst (B x y)) := by
  rw [symmetricComponent_apply, jAction_apply, B.smul_left, Q.snd_j_mul_any]

/-- Multiplication by the second generator is a semisimilarity of the symmetric component. -/
theorem symmetricComponent_jAction_both (x y : V) :
    Q.symmetricComponent B hbar (Q.jAction x) (Q.jAction y) =
      -d * κ (Q.symmetricComponent B hbar x y) := by
  rw [symmetricComponent_apply, jAction_apply, jAction_apply, B.smul_left, B.smul_right,
    hbar, Q.bar_j, ← mul_assoc, mul_neg, map_neg, map_neg, Q.snd_mul_j, Q.fst_j_mul_any,
    SU3Root.conjugation_involutive, symmetricComponent_apply, SU3Root.conjugation_involutive,
    neg_mul]

/-- Skew isotropy is simultaneous vanishing of the two scalar component values. -/
theorem skew_self_eq_zero_iff (x : V) :
    B x x = 0 ↔ Q.symmetricComponent B hbar x x = 0 ∧ Q.symmetricComponent B hbar (Q.jAction x) x = 0 := by
  rw [symmetricComponent_apply, symmetricComponent_jAction_left]
  constructor
  · intro h
    simp [h]
  · rintro ⟨hs, hf⟩
    have hs0 : Q.snd (B x x) = 0 := (κ).injective (hs.trans (map_zero _).symm)
    have hf0 : Q.fst (B x x) = 0 := (κ).injective (hf.trans (map_zero _).symm)
    rw [← Q.decompose (B x x), hf0, hs0, map_zero, mul_zero, add_zero]

/-- Translating the second argument gives minus the first quaternion coordinate. -/
theorem symmetricComponent_jAction_right (x y : V) :
    Q.symmetricComponent B hbar x (Q.jAction y) = -Q.fst (B x y) := by
  rw [Q.symmetricComponent_swap B hbar (Q.jAction y) x, Q.symmetricComponent_jAction_left B hbar,
    B.skew x y, map_neg, hbar, Q.fst_bar, map_neg, SU3Root.conjugation_involutive]

/-- On two vectors from a totally isotropic subspace of the symmetric component,
  the skew self-pairing of `u + j·v` vanishes exactly when the two mixed component
  equations hold. -/
theorem skew_self_add_jAction_eq_zero_iff (h2 : (2 : E) ≠ 0) (u v : V)
    (hu : Q.symmetricComponent B hbar u u = 0)
    (hv : Q.symmetricComponent B hbar v v = 0)
    (huv : Q.symmetricComponent B hbar u v = 0) :
    B (u + Q.jAction v) (u + Q.jAction v) = 0 ↔
      Q.symmetricComponent B hbar u (Q.jAction v) = 0 ∧
      Q.symmetricComponent B hbar u (Q.jAction u) +
        d * Q.symmetricComponent B hbar v (Q.jAction v) = 0 := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let C := Q.symmetricComponent B hbar
  let T := Q.jAction (V := V)
  have hSymm (x y : V) : C x y = C y x := Q.symmetricComponent_swap B hbar y x
  have hu0 : C u u = 0 := hu
  have hv0 : C v v = 0 := hv
  have huv0 : C u v = 0 := huv
  have hvu0 : C v u = 0 := (hSymm v u).trans huv
  have htv : C (T v) (T v) = 0 := by
    change Q.symmetricComponent B hbar (Q.jAction v) (Q.jAction v) = 0
    rw [Q.symmetricComponent_jAction_both B hbar, hv, map_zero, mul_zero]
  have htu : C (T u) (T v) = 0 := by
    change Q.symmetricComponent B hbar (Q.jAction u) (Q.jAction v) = 0
    rw [Q.symmetricComponent_jAction_both B hbar, huv, map_zero, mul_zero]
  have h₁ : C (u + T v) (u + T v) = 2 * C u (T v) := by
    simp only [map_add, LinearMap.add_apply, hu0, htv, zero_add, add_zero, hSymm (T v) u, two_mul]
  have h₂ : C (T (u + T v)) (u + T v) = C u (T u) + d * C v (T v) := by
    have hT : T (T v) = d • v := Q.jAction_sq v
    simp only [map_add, LinearMap.add_apply, hT, map_smul, LinearMap.smul_apply, smul_eq_mul, htu,
      hvu0, mul_zero, add_zero, zero_add, hSymm (T u) u]
  rw [Q.skew_self_eq_zero_iff B hbar]
  change (C (u + T v) (u + T v) = 0 ∧ C (T (u + T v)) (u + T v) = 0) ↔ _
  rw [h₁, h₂, mul_eq_zero]
  exact and_congr (or_iff_right h2) Iff.rfl

end Langlands.GroupScheme.KneserThree.QuatData
