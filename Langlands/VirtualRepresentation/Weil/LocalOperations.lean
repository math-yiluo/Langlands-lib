import Langlands.VirtualRepresentation.Weil.Local
import Langlands.VirtualRepresentation.Weil.Twist
import Langlands.VirtualRepresentation.Weil.Dual

/-! # Actual local Weil lattice operations and unramified orbits -/

noncomputable section

universe uF uV

namespace Langlands.VirtualRepresentation.LocalWeil

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Twist actual local irreducible classes by an actual continuous character. -/
def twistBasisEquiv (χ : localWeilGroup F →ₜ* ℂˣ) :
    Basis.{uF, uV} F ≃ Basis.{uF, uV} F :=
  Weil.twistBasisEquiv χ

/-- Extend the actual local character twist by integer linearity. -/
def twistLatticeEquiv (χ : localWeilGroup F →ₜ* ℂˣ) :
    Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  Weil.twistLatticeEquiv χ

@[simp] theorem twistBasisEquiv_rank (χ : localWeilGroup F →ₜ* ℂˣ)
    (b : Basis.{uF, uV} F) : (twistBasisEquiv F χ b).1 = b.1 := rfl

@[simp] theorem underlyingClass_twistBasisEquiv
    (χ : localWeilGroup F →ₜ* ℂˣ) (b : Basis.{uF, uV} F) :
    Weil.underlyingClass (localWeilGroup F) (twistBasisEquiv F χ b) =
      FiniteRepresentation.twistClass χ.toMonoidHom
        (Weil.underlyingClass (localWeilGroup F) b) :=
  Weil.underlyingClass_twistBasisEquiv χ b

@[simp] theorem twistLatticeEquiv_one :
    twistLatticeEquiv F (1 : localWeilGroup F →ₜ* ℂˣ) =
      LinearEquiv.refl ℤ (Lattice.{uF, uV} F) :=
  Weil.twistLatticeEquiv_one

theorem twistLatticeEquiv_mul (χ η : localWeilGroup F →ₜ* ℂˣ) :
    (twistLatticeEquiv.{uF, uV} F η).trans (twistLatticeEquiv F χ) =
      twistLatticeEquiv F (χ * η) :=
  Weil.twistLatticeEquiv_mul χ η

@[simp] theorem twistLatticeEquiv_symm (χ : localWeilGroup F →ₜ* ℂˣ) :
    (twistLatticeEquiv.{uF, uV} F χ).symm = twistLatticeEquiv F χ⁻¹ :=
  Weil.twistLatticeEquiv_symm χ

@[simp] theorem twistLatticeEquiv_generator (χ : localWeilGroup F →ₜ* ℂˣ)
    (b : Basis.{uF, uV} F) :
    twistLatticeEquiv F χ (generator b) = generator (twistBasisEquiv F χ b) :=
  Weil.twistLatticeEquiv_generator χ b

@[simp] theorem twistLatticeEquiv_coefficient (χ : localWeilGroup F →ₜ* ℂˣ)
    (x : Lattice.{uF, uV} F) (b : Basis.{uF, uV} F) :
    twistLatticeEquiv F χ x (twistBasisEquiv F χ b) = x b :=
  Weil.twistLatticeEquiv_coefficient χ x b

@[simp] theorem degree_twistLatticeEquiv (χ : localWeilGroup F →ₜ* ℂˣ)
    (x : Lattice.{uF, uV} F) :
    degree F (twistLatticeEquiv F χ x) = degree F x :=
  Weil.degree_twistLatticeEquiv χ x

theorem multiplicityPairing_twistLatticeEquiv
    (χ : localWeilGroup F →ₜ* ℂˣ) (x y : Lattice.{uF, uV} F) :
    multiplicityPairing F (twistLatticeEquiv F χ x) (twistLatticeEquiv F χ y) =
      multiplicityPairing F x y :=
  Weil.multiplicityPairing_twistLatticeEquiv χ x y

theorem effective_twistLatticeEquiv_iff (χ : localWeilGroup F →ₜ* ℂˣ)
    (x : Lattice.{uF, uV} F) :
    twistLatticeEquiv F χ x ∈ effective F ↔ x ∈ effective F :=
  Weil.effective_twistLatticeEquiv_iff χ x

/-- Actual contragredience on the positive-rank local Weil basis. -/
def dualBasisEquiv : Basis.{uF, uV} F ≃ Basis.{uF, uV} F :=
  Weil.dualBasisEquiv

/-- The integer-linear local contragredient involution. -/
def dualLatticeEquiv : Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  Weil.dualLatticeEquiv

@[simp] theorem dualBasisEquiv_rank (b : Basis.{uF, uV} F) :
    (dualBasisEquiv F b).1 = b.1 := rfl

@[simp] theorem underlyingClass_dualBasisEquiv (b : Basis.{uF, uV} F) :
    Weil.underlyingClass (localWeilGroup F) (dualBasisEquiv F b) =
      FiniteRepresentation.dualClass (Weil.underlyingClass (localWeilGroup F) b) :=
  Weil.underlyingClass_dualBasisEquiv b

@[simp] theorem dualBasisEquiv_apply_apply (b : Basis.{uF, uV} F) :
    dualBasisEquiv F (dualBasisEquiv F b) = b :=
  Weil.dualBasisEquiv_apply_apply b

@[simp] theorem dualLatticeEquiv_apply_apply (x : Lattice.{uF, uV} F) :
    dualLatticeEquiv F (dualLatticeEquiv F x) = x :=
  Weil.dualLatticeEquiv_apply_apply x

@[simp] theorem dualLatticeEquiv_symm :
    (dualLatticeEquiv.{uF, uV} F).symm = dualLatticeEquiv F :=
  Weil.dualLatticeEquiv_symm

@[simp] theorem dualLatticeEquiv_generator (b : Basis.{uF, uV} F) :
    dualLatticeEquiv F (generator b) = generator (dualBasisEquiv F b) :=
  Weil.dualLatticeEquiv_generator b

@[simp] theorem dualLatticeEquiv_coefficient
    (x : Lattice.{uF, uV} F) (b : Basis.{uF, uV} F) :
    dualLatticeEquiv F x (dualBasisEquiv F b) = x b :=
  Weil.dualLatticeEquiv_coefficient x b

@[simp] theorem degree_dualLatticeEquiv (x : Lattice.{uF, uV} F) :
    degree F (dualLatticeEquiv F x) = degree F x :=
  Weil.degree_dualLatticeEquiv x

theorem multiplicityPairing_dualLatticeEquiv (x y : Lattice.{uF, uV} F) :
    multiplicityPairing F (dualLatticeEquiv F x) (dualLatticeEquiv F y) =
      multiplicityPairing F x y :=
  Weil.multiplicityPairing_dualLatticeEquiv x y

theorem effective_dualLatticeEquiv_iff (x : Lattice.{uF, uV} F) :
    dualLatticeEquiv F x ∈ effective F ↔ x ∈ effective F :=
  Weil.effective_dualLatticeEquiv_iff x

/-- Twist by the unramified character with value `z` at geometric Frobenius. -/
def unramifiedTwistLatticeEquiv (z : ℂˣ) :
    Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  twistLatticeEquiv F (localUnramifiedCharacter F z)

/-- Twist by the actual residue-cardinality-normalized norm character. -/
def normTwistLatticeEquiv :
    Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  twistLatticeEquiv F (localNormCharacter F)

theorem normTwistLatticeEquiv_eq_unramified :
    normTwistLatticeEquiv.{uF, uV} F =
      unramifiedTwistLatticeEquiv F (residueCardinalityUnit F.canonicalTopologicalData)⁻¹ :=
  rfl

/-- Orbits under every complex unramified twist of the actual local Weil group. -/
abbrev UnramifiedOrbitClasses := Weil.UnramifiedOrbitClasses.{uF, uV} (localDegree F)

def unramifiedOrbitClass (b : Basis.{uF, uV} F) : UnramifiedOrbitClasses.{uF, uV} F :=
  Weil.unramifiedOrbitClass (localDegree F) b

theorem unramifiedOrbitClass_eq_iff (a b : Basis.{uF, uV} F) :
    unramifiedOrbitClass F a = unramifiedOrbitClass F b ↔
      ∃ z : ℂˣ, twistBasisEquiv F (localUnramifiedCharacter F z) b = a :=
  Weil.unramifiedOrbitClass_eq_iff (localDegree F) a b

/-- Add the actual irreducible coefficients within each unramified orbit. -/
def unramifiedOrbitMap :
    Lattice.{uF, uV} F →ₗ[ℤ] IntegralLattice (UnramifiedOrbitClasses.{uF, uV} F) :=
  Weil.unramifiedOrbitMap (localDegree F)

@[simp] theorem unramifiedOrbitMap_generator (b : Basis.{uF, uV} F) :
    unramifiedOrbitMap F (generator b) = generator (unramifiedOrbitClass F b) := by
  simp [unramifiedOrbitMap, unramifiedOrbitClass, Weil.unramifiedOrbitMap, map, generator]

/-- Positive representation dimension on actual unramified orbits. -/
def unramifiedOrbitRank : UnramifiedOrbitClasses.{uF, uV} F → ℕ+ :=
  Weil.unramifiedOrbitRank (localDegree F)

@[simp] theorem unramifiedOrbitRank_class (b : Basis.{uF, uV} F) :
    unramifiedOrbitRank F (unramifiedOrbitClass F b) = b.1 := rfl

/-- Actual orbit classes in a specified rank, without finiteness assumptions. -/
def unramifiedOrbitRankStratum (n : ℕ+) : Set (UnramifiedOrbitClasses.{uF, uV} F) :=
  Weil.unramifiedOrbitRankStratum (localDegree F) n

end Langlands.VirtualRepresentation.LocalWeil
