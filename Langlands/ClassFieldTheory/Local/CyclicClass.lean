import Langlands.ClassFieldTheory.Local.Cohomology
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Explicit cyclic classes in relative Galois cohomology

The carry cocycle uses the character sending the chosen positive generator
to `1/n`, and the actual inclusion of base-field units into extension units.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- The carry in addition of the standard representatives modulo `n`. -/
def cyclicCarry {n : ℕ} (a b : ZMod n) : ℕ :=
  (a.val + b.val) / n

theorem cyclicCarry_spec {n : ℕ} [NeZero n] (a b : ZMod n) :
    n * cyclicCarry a b + (a + b).val = a.val + b.val := by
  simpa only [cyclicCarry, ZMod.val_add] using Nat.div_add_mod (a.val + b.val) n

theorem cyclicCarry_assoc {n : ℕ} [NeZero n] (a b c : ZMod n) :
    cyclicCarry (a + b) c + cyclicCarry a b =
      cyclicCarry b c + cyclicCarry a (b + c) := by
  have h₁ := cyclicCarry_spec a b
  have h₂ := cyclicCarry_spec (a + b) c
  have h₃ := cyclicCarry_spec b c
  have h₄ := cyclicCarry_spec a (b + c)
  rw [add_assoc] at h₂
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos n)
  nlinarith

/-- The carry has the positive coboundary sign for the lift of `r/n mod ℤ`. -/
theorem cyclicCarry_rational {n : ℕ} [NeZero n] (a b : ZMod n) :
    (cyclicCarry a b : ℚ) =
      (a.val : ℚ) / n + (b.val : ℚ) / n - ((a + b).val : ℚ) / n := by
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h := congrArg (fun m : ℕ => (m : ℚ)) (cyclicCarry_spec a b)
  push_cast at h
  field_simp
  nlinarith

/-- A base-field unit, viewed in the actual additive Galois coefficient module. -/
def baseUnit (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
    (a : Kˣ) : unitsRepresentation K L :=
  Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a)

theorem baseUnit_fixed (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] (a : Kˣ) (σ : Gal(L/K)) :
    (unitsRepresentation K L).ρ σ (baseUnit K L a) = baseUnit K L a := by
  apply Units.ext
  exact σ.commutes (a : K)

/-- The genuine unit-valued carry cocycle for a cyclic character. -/
def cyclicUnitCocycle (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n]
    (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    groupCohomology.cocycles₂ (unitsRepresentation K L) :=
  ⟨fun gh => cyclicCarry (χ gh.1).toAdd (χ gh.2).toAdd • baseUnit K L a, by
    apply (groupCohomology.mem_cocycles₂_iff _).2
    intro g h j
    simp only [map_mul, toAdd_mul, map_nsmul, baseUnit_fixed]
    rw [← add_nsmul, ← add_nsmul, cyclicCarry_assoc]⟩

/-- The class of the explicit positive carry cocycle in actual relative `H²`. -/
def cyclicClass (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n]
    (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    relativeCohomology K L 2 :=
  groupCohomology.H2π (unitsRepresentation K L) (cyclicUnitCocycle K L χ a)

end Langlands.ClassFieldTheory.Local
