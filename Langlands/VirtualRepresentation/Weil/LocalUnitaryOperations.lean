import Langlands.VirtualRepresentation.Weil.LocalOperations
import Langlands.VirtualRepresentation.Weil.UnitaryOperations

/-! # Actual local unitary Weil lattice operations -/

noncomputable section

universe uF uV

namespace Langlands.VirtualRepresentation.LocalWeil

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Twist genuine local unitary classes by a modulus-one continuous character. -/
def unitaryTwistBasisEquiv (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) :
    UnitaryBasis.{uF, uV} F ≃ UnitaryBasis.{uF, uV} F :=
  Weil.unitaryTwistBasisEquiv χ hχ

/-- The corresponding integer-linear operation on the actual unitary lattice. -/
def unitaryTwistLatticeEquiv (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) :
    UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  Weil.unitaryTwistLatticeEquiv χ hχ

@[simp] theorem unitaryTwistBasisEquiv_val (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (b : UnitaryBasis.{uF, uV} F) :
    (unitaryTwistBasisEquiv F χ hχ b).val = twistBasisEquiv F χ b.val := rfl

@[simp] theorem unitaryTwistBasisEquiv_rank (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (b : UnitaryBasis.{uF, uV} F) :
    (unitaryTwistBasisEquiv F χ hχ b).val.1 = b.val.1 := rfl

@[simp] theorem unitaryTwistBasisEquiv_one :
    unitaryTwistBasisEquiv F (1 : localWeilGroup F →ₜ* ℂˣ) (by intro w; simp) =
      Equiv.refl (UnitaryBasis.{uF, uV} F) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  change Weil.twistBasisEquiv (1 : localWeilGroup F →ₜ* ℂˣ) b.val = b.val
  simp

/-- Products of actual modulus-one local characters remain modulus one. -/
theorem norm_mul_character_eq_one (χ η : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (hη : ∀ w, ‖(η w : ℂ)‖ = 1) (w) :
    ‖((χ * η) w : ℂ)‖ = 1 := by
  change ‖(χ w : ℂ) * (η w : ℂ)‖ = 1
  simp [hχ w, hη w]

theorem unitaryTwistBasisEquiv_mul (χ η : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (hη : ∀ w, ‖(η w : ℂ)‖ = 1) :
    (unitaryTwistBasisEquiv.{uF, uV} F η hη).trans (unitaryTwistBasisEquiv F χ hχ) =
      unitaryTwistBasisEquiv F (χ * η) (norm_mul_character_eq_one F χ η hχ hη) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (Weil.twistBasisEquiv_mul χ η) b.val

@[simp] theorem unitaryTwistLatticeEquiv_one :
    unitaryTwistLatticeEquiv F (1 : localWeilGroup F →ₜ* ℂˣ) (by intro w; simp) =
      LinearEquiv.refl ℤ (UnitaryLattice.{uF, uV} F) := by
  change reindex (unitaryTwistBasisEquiv F 1 _) = _
  simp [reindex]

theorem unitaryTwistLatticeEquiv_mul (χ η : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (hη : ∀ w, ‖(η w : ℂ)‖ = 1) :
    (unitaryTwistLatticeEquiv.{uF, uV} F η hη).trans (unitaryTwistLatticeEquiv F χ hχ) =
      unitaryTwistLatticeEquiv F (χ * η) (norm_mul_character_eq_one F χ η hχ hη) := by
  change (reindex (unitaryTwistBasisEquiv F η hη)).trans
    (reindex (unitaryTwistBasisEquiv F χ hχ)) = reindex _
  simp only [reindex, Finsupp.domLCongr_trans, unitaryTwistBasisEquiv_mul]
  rfl

@[simp] theorem unitaryTwistLatticeEquiv_symm (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) :
    (unitaryTwistLatticeEquiv.{uF, uV} F χ hχ).symm =
      unitaryTwistLatticeEquiv F χ⁻¹ (Weil.norm_inv_character_eq_one χ hχ) :=
  Weil.unitaryTwistLatticeEquiv_symm χ hχ

@[simp] theorem unitaryTwistLatticeEquiv_generator (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (b : UnitaryBasis.{uF, uV} F) :
    unitaryTwistLatticeEquiv F χ hχ (generator b) =
      generator (unitaryTwistBasisEquiv F χ hχ b) :=
  Weil.unitaryTwistLatticeEquiv_generator χ hχ b

@[simp] theorem unitaryTwistLatticeEquiv_coefficient (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (x : UnitaryLattice.{uF, uV} F)
    (b : UnitaryBasis.{uF, uV} F) :
    unitaryTwistLatticeEquiv F χ hχ x (unitaryTwistBasisEquiv F χ hχ b) = x b :=
  Weil.unitaryTwistLatticeEquiv_coefficient χ hχ x b

@[simp] theorem includeUnitary_twist (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (x : UnitaryLattice.{uF, uV} F) :
    includeUnitary F (unitaryTwistLatticeEquiv F χ hχ x) =
      twistLatticeEquiv F χ (includeUnitary F x) :=
  Weil.includeUnitary_twist χ hχ x

@[simp] theorem unitaryDegree_twist (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (x : UnitaryLattice.{uF, uV} F) :
    unitaryDegree F (unitaryTwistLatticeEquiv F χ hχ x) = unitaryDegree F x :=
  Weil.unitaryDegree_twist χ hχ x

theorem unitaryPairing_twist (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (x y : UnitaryLattice.{uF, uV} F) :
    unitaryPairing F (unitaryTwistLatticeEquiv F χ hχ x)
      (unitaryTwistLatticeEquiv F χ hχ y) = unitaryPairing F x y :=
  Weil.unitaryPairing_twist χ hχ x y

theorem effective_unitaryTwist_iff (χ : localWeilGroup F →ₜ* ℂˣ)
    (hχ : ∀ w, ‖(χ w : ℂ)‖ = 1) (x : UnitaryLattice.{uF, uV} F) :
    unitaryTwistLatticeEquiv F χ hχ x ∈ VirtualRepresentation.effective ↔
      x ∈ VirtualRepresentation.effective :=
  Weil.effective_unitaryTwist_iff χ hχ x

/-- Actual contragredience on local unitary classes. -/
def unitaryDualBasisEquiv : UnitaryBasis.{uF, uV} F ≃ UnitaryBasis.{uF, uV} F :=
  Weil.unitaryDualBasisEquiv

/-- The integer-linear contragredient involution on the local unitary lattice. -/
def unitaryDualLatticeEquiv : UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  Weil.unitaryDualLatticeEquiv

@[simp] theorem unitaryDualBasisEquiv_val (b : UnitaryBasis.{uF, uV} F) :
    (unitaryDualBasisEquiv F b).val = dualBasisEquiv F b.val := rfl

@[simp] theorem unitaryDualBasisEquiv_rank (b : UnitaryBasis.{uF, uV} F) :
    (unitaryDualBasisEquiv F b).val.1 = b.val.1 := rfl

@[simp] theorem unitaryDualBasisEquiv_apply_apply (b : UnitaryBasis.{uF, uV} F) :
    unitaryDualBasisEquiv F (unitaryDualBasisEquiv F b) = b :=
  Weil.unitaryDualBasisEquiv_apply_apply b

@[simp] theorem unitaryDualLatticeEquiv_apply_apply (x : UnitaryLattice.{uF, uV} F) :
    unitaryDualLatticeEquiv F (unitaryDualLatticeEquiv F x) = x :=
  Weil.unitaryDualLatticeEquiv_apply_apply x

@[simp] theorem unitaryDualLatticeEquiv_symm :
    (unitaryDualLatticeEquiv.{uF, uV} F).symm = unitaryDualLatticeEquiv F :=
  Weil.unitaryDualLatticeEquiv_symm

@[simp] theorem unitaryDualLatticeEquiv_generator (b : UnitaryBasis.{uF, uV} F) :
    unitaryDualLatticeEquiv F (generator b) = generator (unitaryDualBasisEquiv F b) :=
  Weil.unitaryDualLatticeEquiv_generator b

@[simp] theorem unitaryDualLatticeEquiv_coefficient (x : UnitaryLattice.{uF, uV} F)
    (b : UnitaryBasis.{uF, uV} F) :
    unitaryDualLatticeEquiv F x (unitaryDualBasisEquiv F b) = x b :=
  Weil.unitaryDualLatticeEquiv_coefficient x b

@[simp] theorem includeUnitary_dual (x : UnitaryLattice.{uF, uV} F) :
    includeUnitary F (unitaryDualLatticeEquiv F x) =
      dualLatticeEquiv F (includeUnitary F x) :=
  Weil.includeUnitary_dual x

@[simp] theorem unitaryDegree_dual (x : UnitaryLattice.{uF, uV} F) :
    unitaryDegree F (unitaryDualLatticeEquiv F x) = unitaryDegree F x :=
  Weil.unitaryDegree_dual x

theorem unitaryPairing_dual (x y : UnitaryLattice.{uF, uV} F) :
    unitaryPairing F (unitaryDualLatticeEquiv F x) (unitaryDualLatticeEquiv F y) =
      unitaryPairing F x y :=
  Weil.unitaryPairing_dual x y

theorem effective_unitaryDual_iff (x : UnitaryLattice.{uF, uV} F) :
    unitaryDualLatticeEquiv F x ∈ VirtualRepresentation.effective ↔
      x ∈ VirtualRepresentation.effective :=
  Weil.effective_unitaryDual_iff x

/-- A modulus-one Frobenius value makes the actual unramified character unitary. -/
theorem norm_localUnramifiedCharacter_eq_one (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (w : localWeilGroup F) : ‖(localUnramifiedCharacter F z w : ℂ)‖ = 1 := by
  change ‖((z ^ (localDegree F w).toAdd : ℂˣ) : ℂ)‖ = 1
  simp [norm_zpow, hz]

/-- The genuine unramified unitary twist, normalized by geometric degree. -/
def unitaryUnramifiedTwistLatticeEquiv (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  unitaryTwistLatticeEquiv F (localUnramifiedCharacter F z)
    (norm_localUnramifiedCharacter_eq_one F z hz)

@[simp] theorem includeUnitary_unramifiedTwist (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (x : UnitaryLattice.{uF, uV} F) :
    includeUnitary F (unitaryUnramifiedTwistLatticeEquiv F z hz x) =
      unramifiedTwistLatticeEquiv F z (includeUnitary F x) :=
  includeUnitary_twist F _ _ x

@[simp] theorem unitaryDegree_unramifiedTwist (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (x : UnitaryLattice.{uF, uV} F) :
    unitaryDegree F (unitaryUnramifiedTwistLatticeEquiv F z hz x) = unitaryDegree F x :=
  unitaryDegree_twist F _ _ x

theorem unitaryPairing_unramifiedTwist (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (x y : UnitaryLattice.{uF, uV} F) :
    unitaryPairing F (unitaryUnramifiedTwistLatticeEquiv F z hz x)
      (unitaryUnramifiedTwistLatticeEquiv F z hz y) = unitaryPairing F x y :=
  unitaryPairing_twist F _ _ x y

end Langlands.VirtualRepresentation.LocalWeil
