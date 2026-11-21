import Langlands.GroupScheme.Quaternionic.SkewHermitianSemilinearComponent

/-! # The induced Hermitian pairing of a skew-hermitian component -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] (Q : QuatData F D)
  {τ : FirstKindInvolution F D} {V : Type v} [AddCommGroup V] [Module D V]
  [Module F V] [IsScalarTower F D V] (B : AntihermitianForm τ V) (hbar : ∀ z, τ z = Q.bar z)

local notation "E" => field Q.c
local notation "κ" => SU3Root.conjugation F E
local notation "d" => algebraMap F E Q.δ

/-- The Hermitian pairing obtained by inserting the second quaternion generator
  into the second argument and multiplying by the skew quadratic root. -/
def inducedHermitian :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    V →ₗ[E] V →ₛₗ[(κ).toRingHom] E := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  exact (root : E) • LinearMap.compl₂ (Q.symmetricComponent B hbar) (Q.jAction (V := V))

@[simp]
theorem inducedHermitian_apply (x y : V) :
    Q.inducedHermitian B hbar x y = (root : E) * Q.symmetricComponent B hbar x (Q.jAction y) := rfl

/-- Interchanging the arguments of the induced pairing conjugates its value. -/
theorem inducedHermitian_conj (x y : V) :
    κ (Q.inducedHermitian B hbar x y) = Q.inducedHermitian B hbar y x := by
  rw [inducedHermitian_apply, inducedHermitian_apply, map_mul, QuadField.conjugation_root,
    Q.symmetricComponent_jAction_right B hbar, map_neg, neg_mul_neg,
    Q.symmetricComponent_swap B hbar (Q.jAction x) y, Q.symmetricComponent_jAction_left B hbar]

private theorem componentRoot_ne_zero : (root : E) ≠ 0 := by
  have hx := Q.basis.ne_zero 1
  rw [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1] at hx
  intro h
  exact hx (by rw [← Q.ι_root, h, map_zero])

/-- Where a totally isotropic subspace and its semilinear image span the space,
  the induced Hermitian pairing restricted to that subspace is left-separating. -/
theorem inducedHermitian_separating_on_subspace (hB : B.toBilin.SeparatingLeft) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∀ W : Submodule E V,
    (∀ x ∈ W, ∀ y ∈ W, Q.symmetricComponent B hbar x y = 0) →
    (∀ z : V, ∃ u ∈ W, ∃ v ∈ W, z = u + Q.jAction v) →
    ∀ x ∈ W, (∀ y ∈ W, Q.inducedHermitian B hbar x y = 0) → x = 0 := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  intro W hW hspan x hx hG
  apply (Q.symmetricComponent_nondegenerate B hbar hB).1 x
  intro y
  obtain ⟨u, hu, v, hv, rfl⟩ := hspan y
  rw [map_add, hW x hx u hu, zero_add]
  have h := hG v hv
  rw [Q.inducedHermitian_apply, mul_eq_zero] at h
  exact h.resolve_left Q.componentRoot_ne_zero

/-- A nonzero vector in a totally isotropic subspace and its semilinear image
  is already isotropic for the skew-hermitian pairing. -/
theorem skew_self_eq_zero_of_subspace_intersection :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∀ W : Submodule E V,
    (∀ x ∈ W, ∀ y ∈ W, Q.symmetricComponent B hbar x y = 0) →
    ∀ x ∈ W, (∃ y ∈ W, Q.jAction y = x) → B x x = 0 := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  intro W hW x hx ⟨y, hy, hxy⟩
  have hTx : Q.jAction x ∈ W := by
    rw [← hxy, Q.jAction_sq]
    exact W.smul_mem d hy
  exact (Q.skew_self_eq_zero_iff B hbar x).mpr ⟨hW x hx x hx, hW (Q.jAction x) hTx x hx⟩

/-- In the paired coordinates, the two equations can be written directly using
  the induced Hermitian pairing. -/
theorem skew_self_add_jAction_eq_zero_iff_inducedHermitian
    (h2 : (2 : E) ≠ 0) (u v : V)
    (hu : Q.symmetricComponent B hbar u u = 0)
    (hv : Q.symmetricComponent B hbar v v = 0)
    (huv : Q.symmetricComponent B hbar u v = 0) :
    B (u + Q.jAction v) (u + Q.jAction v) = 0 ↔
      Q.inducedHermitian B hbar u v = 0 ∧
      Q.inducedHermitian B hbar u u + d * Q.inducedHermitian B hbar v v = 0 := by
  rw [Q.skew_self_add_jAction_eq_zero_iff B hbar h2 u v hu hv huv]
  simp only [inducedHermitian_apply]
  have h : (root : E) * Q.symmetricComponent B hbar u (Q.jAction u) +
      d * ((root : E) * Q.symmetricComponent B hbar v (Q.jAction v)) =
      (root : E) * (Q.symmetricComponent B hbar u (Q.jAction u) +
        d * Q.symmetricComponent B hbar v (Q.jAction v)) := by ring
  rw [h]
  simp only [mul_eq_zero, Q.componentRoot_ne_zero, false_or]

end Langlands.GroupScheme.KneserThree.QuatData
