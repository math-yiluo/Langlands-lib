import Langlands.Galois.ClosureRestriction
import Langlands.Galois.FrobeniusLift
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! # The cyclotomic character on actual geometric Frobenius lifts -/

noncomputable section

namespace Langlands.GaloisRepresentation

open Langlands.Global IsLocalRing
open scoped Valued

universe uK uE

variable (p : ℕ) [Fact p.Prime]
variable (K : Type uK) [Field K]

/-- Mathlib's cyclotomic character on the actual absolute Galois group. -/
def absoluteCyclotomicCharacter : Field.absoluteGaloisGroup K →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (AlgebraicClosure K) p).comp
    (MulSemiringAction.toRingAut Gal(AlgebraicClosure K/K) (AlgebraicClosure K))

theorem continuous_absoluteCyclotomicCharacter :
    Continuous (absoluteCyclotomicCharacter p K) :=
  cyclotomicCharacter.continuous p K (AlgebraicClosure K)

variable [CharZero K]

private theorem absoluteCyclotomicCharacter_action (g : Field.absoluteGaloisGroup K)
    (n : ℕ) (x : AlgebraicClosure K) (hx : x ^ p ^ n = 1) :
    AlgEquiv.toRingEquiv g x = x ^ (((absoluteCyclotomicCharacter p K g).val.toZModPow n).val) :=
  cyclotomicCharacter.spec p (AlgEquiv.toRingEquiv g) x hx

private theorem zmod_eq_of_primitiveRoot_pow_eq {F : Type*} [Field F]
    {n : ℕ} [NeZero n] {x : F} (hx : IsPrimitiveRoot x n) (a b : ZMod n)
    (h : x ^ a.val = x ^ b.val) : a = b := by
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b,
    ZMod.natCast_eq_natCast_iff]
  simpa only [← hx.eq_orderOf] using (hx.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq.mp h

private theorem absoluteCyclotomicCharacter_val_eq_natCast (g : Field.absoluteGaloisGroup K)
    (a : ℕ) (h : ∀ (n : ℕ) (x : AlgebraicClosure K), x ^ p ^ n = 1 →
      AlgEquiv.toRingEquiv g x = x ^ a) :
    (absoluteCyclotomicCharacter p K g).val = a := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [map_natCast]
  obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (p ^ n)
  apply zmod_eq_of_primitiveRoot_pow_eq hx
  rw [← absoluteCyclotomicCharacter_action p K g n x hx.pow_eq_one, h n x hx.pow_eq_one,
    ZMod.val_natCast]
  exact (pow_eq_pow_of_modEq (Nat.mod_modEq a (p ^ n)) hx.pow_eq_one).symm

variable {K}

/-- The character commutes with actual absolute Galois restriction. -/
theorem absoluteCyclotomicCharacter_map {E : Type uE} [Field E] [CharZero E]
    (f : K →+* E) (g : Field.absoluteGaloisGroup E) :
    absoluteCyclotomicCharacter p K (Field.absoluteGaloisGroup.map f g) =
      absoluteCyclotomicCharacter p E g := by
  let : Algebra K E := f.toAlgebra
  let j : AlgebraicClosure K →ₐ[K] AlgebraicClosure E := chosenClosureEmbedding f
  rw [← restrictionAlongClosure_chosen_eq f]
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (p ^ n)
  apply zmod_eq_of_primitiveRoot_pow_eq hx
  apply j.injective
  rw [map_pow, map_pow]
  change (j x) ^ _ = (j x) ^ _
  have hjx : (j x) ^ p ^ n = 1 := by rw [← map_pow, hx.pow_eq_one, map_one]
  rw [← absoluteCyclotomicCharacter_action p E g n (j x) hjx,
    ← map_pow, ← absoluteCyclotomicCharacter_action p K _ n x hx.pow_eq_one]
  exact restrictionAlongClosure_commutes j g x

section FinitePlace

variable [NumberField K] (v : FinitePlace K)

local notation "Kv" => FiniteCompletion K v
local notation "Ω" => AlgebraicClosure (FiniteCompletion K v)
local notation "A" =>
  LocalGalois.extensionIntegers (FiniteCompletion K v) (AlgebraicClosure (FiniteCompletion K v))

local instance : CharZero Kv := Algebra.charZero_of_charZero K Kv

private theorem primePower_isUnit (hchar : residueCharacteristic v ≠ p) (n : ℕ) :
    IsUnit ((p ^ n : ℕ) : A) := by
  let k := ResidueField (LocalGalois.baseIntegers Kv)
  let : CharP k (residueCharacteristic v) := by
    change CharP k (ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal))
    rw [← Global.CompletionResidue.ringChar_residueField K v]
    infer_instance
  have : CharP (LocalResidueClosure v) (residueCharacteristic v) :=
    ((algebraMap k (LocalResidueClosure v)).charP_iff
      (algebraMap k (LocalResidueClosure v)).injective (residueCharacteristic v)).mp inferInstance
  rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_pow]
  apply pow_ne_zero
  intro hp
  exact hchar ((Nat.prime_dvd_prime_iff_eq (CharP.prime_ringChar
    (NumberField.RingOfIntegers K ⧸ v.asIdeal)) (Fact.out : p.Prime)).mp
      ((CharP.cast_eq_zero_iff (LocalResidueClosure v) (residueCharacteristic v) p).mp hp))

private theorem integerOfPowerEqOne {n : ℕ} {x : Ω} (hn : n ≠ 0) (hx : x ^ n = 1) :
    x ∈ A := by
  rw [Valuation.mem_valuationSubring_iff]
  by_contra h
  push Not at h
  have hpow := one_lt_pow₀ h hn
  rw [← map_pow, hx, map_one] at hpow
  exact lt_irrefl _ hpow

private theorem absoluteCyclotomicCharacter_val_eq_of_residue_pow
    (hchar : residueCharacteristic v ≠ p) (g : LocalGroup v) (a : ℕ)
    (hg : ∀ x : LocalResidueClosure v, localResidueAction v g x = x ^ a) :
    (absoluteCyclotomicCharacter p Kv g).val = a := by
  apply absoluteCyclotomicCharacter_val_eq_natCast
  intro n x hx
  let z : A := ⟨x, integerOfPowerEqOne v (pow_ne_zero n (Fact.out : p.Prime).ne_zero) hx⟩
  have hz : z ^ p ^ n = 1 := Subtype.ext hx
  let σ := LocalGalois.integerAut Kv Ω g
  have hgz : (σ z) ^ p ^ n = 1 := by rw [← map_pow, hz, map_one]
  have hza : (z ^ a) ^ p ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have hres : residue A (σ z) = residue A (z ^ a) := by
    change localResidueAction v g (residue A z) = residue A (z ^ a)
    rw [map_pow]
    exact hg (residue A z)
  exact congrArg Subtype.val (LocalGalois.Separable.eq_of_pow_eq_one_of_sub_mem
    (primePower_isUnit p v hchar n) hgz hza
    (by rw [← residue_eq_zero_iff, map_sub, hres, sub_self]))

/-- The character is trivial on the actual local inertia away from its prime. -/
theorem absoluteCyclotomicCharacter_inertia (hchar : residueCharacteristic v ≠ p)
    (g : localInertia v) : absoluteCyclotomicCharacter p Kv g.val = 1 := by
  apply Units.ext
  apply absoluteCyclotomicCharacter_val_eq_of_residue_pow p v hchar g.val 1
  intro x
  rw [show localResidueAction v g.val = 1 from g.property, pow_one]
  rfl

/-- On the inverse of a geometric lift the character has value equal to the
    residue cardinality, as a p-adic integer. -/
theorem absoluteCyclotomicCharacter_geometricFrobenius_inv
    (hchar : residueCharacteristic v ≠ p) {g : LocalGroup v}
    (hg : IsGeometricFrobeniusLift v g) :
    (absoluteCyclotomicCharacter p Kv g⁻¹).val = residueCardinality v :=
  absoluteCyclotomicCharacter_val_eq_of_residue_pow p v hchar g⁻¹ _ hg

end FinitePlace
end Langlands.GaloisRepresentation
