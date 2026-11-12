import Langlands.Shimura.Unitary.Similitude

/-!
# Similitudes split by a central idempotent exchanged by the involution

Let `τ` be an involution of an `S`-algebra `B` and let `e` be a central
idempotent of `B` with `τ e = 1 - e`. If `π : B → Q` is a ring homomorphism
with a multiplicative section `ψ` satisfying `π ∘ ψ = id` and `ψ ∘ π = e · -`,
then the similitude group of `τ` is `Qˣ × Sˣ`: a similitude is determined by
the image of its algebra unit in `Q` and its multiplier.
-/

noncomputable section

set_option autoImplicit false

universe u v w

namespace Langlands.Shimura.AlgebraInvolution

variable {S : Type u} {B : Type v} [CommRing S] [Ring B] [Algebra S B]

/-- A central idempotent `e` exchanged with `1 - e` by the involution, a ring
homomorphism `π` and a multiplicative section `ψ` with `π ∘ ψ = id` and
`ψ ∘ π = e · -`. -/
structure CentralExchangeSplitting (τ : AlgebraInvolution S B) (Q : Type w) [Ring Q] where
  /-- The central idempotent. -/
  idempotent : B
  idempotent_mul_self : idempotent * idempotent = idempotent
  idempotent_mul_comm (x : B) : idempotent * x = x * idempotent
  involution_idempotent : τ idempotent = 1 - idempotent
  /-- The projection onto the factor cut out by the idempotent. -/
  projection : B →+* Q
  /-- The multiplicative section of the projection, with image in `e B`. -/
  lift : Q → B
  lift_mul (x y : Q) : lift (x * y) = lift x * lift y
  projection_lift (x : Q) : projection (lift x) = x
  lift_projection (x : B) : lift (projection x) = idempotent * x

namespace CentralExchangeSplitting

variable {τ : AlgebraInvolution S B} {Q : Type w} [Ring Q]
variable (P : CentralExchangeSplitting τ Q)

local notation "e" => P.idempotent
local notation "π" => P.projection
local notation "ψ" => P.lift

theorem lift_one : ψ 1 = e := by
  simpa using P.lift_projection 1

theorem projection_idempotent : π e = 1 := by
  rw [← P.lift_one, P.projection_lift]

theorem projection_one_sub_idempotent : π (1 - e) = 0 := by
  rw [_root_.map_sub, _root_.map_one, P.projection_idempotent, sub_self]

theorem idempotent_mul_lift (x : Q) : e * ψ x = ψ x := by
  rw [← P.lift_projection, P.projection_lift]

theorem lift_mul_idempotent (x : Q) : ψ x * e = ψ x := by
  rw [← P.idempotent_mul_comm, P.idempotent_mul_lift]

theorem idempotent_mul_one_sub : e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, P.idempotent_mul_self, sub_self]

theorem involution_lift_mul_one_sub (x : Q) : τ (ψ x) * (1 - e) = τ (ψ x) := by
  rw [← P.involution_idempotent, ← τ.apply_mul, P.idempotent_mul_lift]

theorem one_sub_mul_involution_lift (x : Q) : (1 - e) * τ (ψ x) = τ (ψ x) := by
  rw [← P.involution_idempotent, ← τ.apply_mul, P.lift_mul_idempotent]

/-- An element of `e B` times an element of `(1 - e) B` vanishes. -/
theorem lift_mul_involution_lift (x y : Q) : ψ x * τ (ψ y) = 0 := by
  rw [← P.lift_mul_idempotent x, ← P.one_sub_mul_involution_lift y, mul_assoc,
    ← mul_assoc e, P.idempotent_mul_one_sub, zero_mul, mul_zero]

/-- An element of `(1 - e) B` times an element of `e B` vanishes. -/
theorem involution_lift_mul_lift (x y : Q) : τ (ψ y) * ψ x = 0 := by
  rw [← P.involution_lift_mul_one_sub y, ← P.idempotent_mul_lift x, mul_assoc,
    ← mul_assoc (1 - e), sub_mul, one_mul, P.idempotent_mul_self, sub_self, zero_mul,
    mul_zero]

theorem involution_lift_mul_involution_lift (x y : Q) :
    τ (ψ x) * τ (ψ y) = τ (ψ (y * x)) := by
  rw [P.lift_mul, τ.apply_mul]

theorem lift_units_mul_inv (a : Qˣ) : ψ a * ψ ↑a⁻¹ = e := by
  rw [← P.lift_mul, Units.mul_inv, P.lift_one]

theorem involution_lift_units_inv_mul (a : Qˣ) : τ (ψ ↑a⁻¹) * τ (ψ a) = 1 - e := by
  rw [P.involution_lift_mul_involution_lift, Units.mul_inv, P.lift_one,
    P.involution_idempotent]

theorem projection_involution_lift (x : Q) : π (τ (ψ x)) = 0 := by
  rw [← P.involution_lift_mul_one_sub x, _root_.map_mul, P.projection_one_sub_idempotent,
    mul_zero]

/-- The value of the inverse construction on a unit of `Q` and a scalar unit. -/
def liftValue (a : Qˣ) (c : Sˣ) : B :=
  ψ a + (c : S) • τ (ψ ↑a⁻¹)

theorem liftValue_mul_liftValue_inv (a : Qˣ) (c : Sˣ) :
    P.liftValue a c * P.liftValue a⁻¹ c⁻¹ = 1 := by
  simp only [liftValue, inv_inv, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    P.lift_units_mul_inv, P.lift_mul_involution_lift, P.involution_lift_mul_lift,
    P.involution_lift_units_inv_mul, smul_zero, add_zero, zero_add, Units.inv_mul, one_smul]
  exact add_sub_cancel _ _

theorem liftValue_mem (a : Qˣ) (c : Sˣ) :
    P.liftValue a c * τ (P.liftValue a c) = algebraMap S B c := by
  simp only [liftValue, τ.apply_add, τ.apply_smul, τ.apply_apply, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, P.lift_units_mul_inv, P.lift_mul_involution_lift,
    P.involution_lift_mul_lift, P.involution_lift_units_inv_mul, smul_zero, add_zero,
    zero_add]
  rw [← smul_add, sub_add_cancel, Algebra.smul_def, mul_one]

/-- The algebra unit attached to a unit of `Q` and a scalar unit. -/
def liftUnit (a : Qˣ) (c : Sˣ) : Bˣ where
  val := P.liftValue a c
  inv := P.liftValue a⁻¹ c⁻¹
  val_inv := P.liftValue_mul_liftValue_inv a c
  inv_val := by simpa using P.liftValue_mul_liftValue_inv a⁻¹ c⁻¹

theorem projection_liftValue (a : Qˣ) (c : Sˣ) : π (P.liftValue a c) = a := by
  rw [liftValue, _root_.map_add, Algebra.smul_def, _root_.map_mul,
    P.projection_involution_lift, mul_zero, add_zero, P.projection_lift]

theorem liftValue_projection (g : τ.similitudes) :
    P.liftValue (Units.map P.projection.toMonoidHom g.1.1) g.1.2 = g.1.1 := by
  have hg := (τ.mem_similitudes_iff g.1).mp g.property
  have hinv : (↑(Units.map P.projection.toMonoidHom g.1.1)⁻¹ : Q) = π ↑g.1.1⁻¹ := by
    rw [← _root_.map_inv]; rfl
  have hτ : (g.1.2 : S) • τ ↑g.1.1⁻¹ = g.1.1 := by
    rw [Algebra.smul_def, ← hg, mul_assoc, ← τ.apply_mul, Units.inv_mul, τ.apply_one,
      mul_one]
  simp only [liftValue, hinv]
  change P.lift (π g.1.1) + _ = _
  rw [P.lift_projection, P.lift_projection, τ.apply_mul, P.involution_idempotent,
    ← smul_mul_assoc, hτ, mul_sub, mul_one, ← P.idempotent_mul_comm]
  abel

/-- The similitude group is the product of the units of `Q` and the scalar
units: the forward map is the projection of the algebra unit together with the
multiplier. -/
def similitudesEquiv : τ.similitudes ≃* Qˣ × Sˣ where
  toFun g := (Units.map P.projection.toMonoidHom g.1.1, g.1.2)
  invFun p := ⟨(P.liftUnit p.1 p.2, p.2),
    (τ.mem_similitudes_iff _).mpr (P.liftValue_mem p.1 p.2)⟩
  left_inv g := by
    apply Subtype.ext
    apply Prod.ext
    · exact Units.ext (P.liftValue_projection g)
    · rfl
  right_inv p := by
    apply Prod.ext
    · exact Units.ext (P.projection_liftValue p.1 p.2)
    · rfl
  map_mul' g h := by
    apply Prod.ext
    · exact _root_.map_mul (Units.map P.projection.toMonoidHom) g.1.1 h.1.1
    · rfl

@[simp] theorem similitudesEquiv_fst_val (g : τ.similitudes) :
    ((P.similitudesEquiv g).1 : Q) = π g.1.1 := rfl

@[simp] theorem similitudesEquiv_snd (g : τ.similitudes) :
    (P.similitudesEquiv g).2 = τ.multiplier g := rfl

@[simp] theorem similitudesEquiv_symm_val (p : Qˣ × Sˣ) :
    ((P.similitudesEquiv.symm p).1.1 : B) = ψ p.1 + (p.2 : S) • τ (ψ ↑p.1⁻¹) := rfl

@[simp] theorem similitudesEquiv_symm_multiplier (p : Qˣ × Sˣ) :
    τ.multiplier (P.similitudesEquiv.symm p) = p.2 := rfl

end CentralExchangeSplitting

end Langlands.Shimura.AlgebraInvolution
