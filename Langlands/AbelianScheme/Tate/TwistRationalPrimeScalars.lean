import Langlands.AbelianScheme.Tate.TwistRationalPrime
import Langlands.AbelianScheme.Tate.TwistPrimeScalars
import Langlands.AbelianScheme.Tate.TwistRationalScalars
import Langlands.Global.RationalProfiniteIntegerPadicProjection

noncomputable section
open scoped TensorProduct

namespace Langlands.TateTwist.Divisibility
universe u v
variable (R : Type u) [CommRing R] (P : ℕ → Prop)

/-- The existing rational residue action as a module for local installation. -/
@[instance_reducible] def rationalScalarModule :
    Module (ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (Rational R P) :=
  Module.compHom _ (rationalScalarAction R P).toRingHom

theorem rationalScalarModule_smul (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing)
    (x : Rational R P) :
    let := rationalScalarModule R P
    a • x = rationalScalarAction R P a x := rfl

theorem rationalScalarModule_scalarTower :
    let := rationalScalarModule R P
    IsScalarTower ℚ (ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (Rational R P) := by
  let := rationalScalarModule R P
  dsimp only
  constructor
  intro q a x
  change rationalScalarAction R P (q • a) x = q • rationalScalarAction R P a x
  simp only [map_smul, LinearMap.smul_apply]

variable (p : ℕ) [Fact p.Prime]

/-- Rational extraction preserves the existing full residue scalar action. -/
theorem rationalToPrime_scalarAction (hP : ∀ n : ℕ, P (p ^ n))
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Rational R P) :
    rationalToPrime R P p hP (rationalScalarAction R P a x) =
      Global.ProfiniteIntegerRing.rationalToPadic p a • rationalToPrime R P p hP x := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      simp only [rationalScalarAction_tmul, rationalToPrime_tmul,
        Global.ProfiniteIntegerRing.rationalToPadic_tmul, toPrime_smul, Rat.cast_mul]
      change ((q : ℚ_[p]) * (r : ℚ_[p])) ⊗ₜ[ℤ_[p]]
          (Global.ProfiniteIntegerRing.toPadic p a • toPrime R P p hP x) =
        (((q : ℚ_[p]) * (Global.ProfiniteIntegerRing.toPadic p a : ℚ_[p])) *
          (r : ℚ_[p])) ⊗ₜ[ℤ_[p]] toPrime R P p hP x
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
    | add x y hx hy => simp_all [smul_add]
  | add a b ha hb => simp_all [add_smul]

/-- The existing rational coordinate map, semilinear over the canonical projection. -/
def rationalToPrimeSemilinear (hP : ∀ n : ℕ, P (p ^ n)) :
    let := rationalScalarModule R P
    Rational R P →ₛₗ[(Global.ProfiniteIntegerRing.rationalToPadic p).toRingHom]
      TateTwist.Rational R p := by
  let := rationalScalarModule R P
  exact { (rationalToPrime R P p hP).toAddHom with
    map_smul' := rationalToPrime_scalarAction R P p hP }

@[simp] theorem rationalToPrimeSemilinear_apply (hP : ∀ n : ℕ, P (p ^ n))
    (x : Rational R P) :
    rationalToPrimeSemilinear R P p hP x = rationalToPrime R P p hP x := rfl

theorem rationalFullToPrime_scalarAction
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : RationalFull R) :
    rationalFullToPrime R p (rationalScalarAction R (fun _ => True) a x) =
      Global.ProfiniteIntegerRing.rationalToPadic p a • rationalFullToPrime R p x :=
  rationalToPrime_scalarAction R (fun _ => True) p (fun _ => trivial) a x

/-- Rational full extraction as a semilinear map. -/
def rationalFullToPrimeSemilinear :
    let := rationalScalarModule R (fun _ => True)
    RationalFull R →ₛₗ[(Global.ProfiniteIntegerRing.rationalToPadic p).toRingHom]
      TateTwist.Rational R p :=
  rationalToPrimeSemilinear R (fun _ => True) p (fun _ => trivial)

@[simp] theorem rationalFullToPrimeSemilinear_apply (x : RationalFull R) :
    rationalFullToPrimeSemilinear R p x = rationalFullToPrime R p x := rfl

/-- The existing away residue action as a module for local installation. -/
@[instance_reducible] def rationalAwayScalarModule (m : ℕ) :
    Module (ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (RationalAway R m) :=
  Module.compHom _ (rationalAwayScalarAction R m).toRingHom

theorem rationalAwayScalarModule_smul (m : ℕ)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (x : RationalAway R m) :
    let := rationalAwayScalarModule R m
    a • x = rationalAwayScalarAction R m a x := rfl

theorem rationalAwayScalarModule_scalarTower (m : ℕ) :
    let := rationalAwayScalarModule R m
    IsScalarTower ℚ (ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (RationalAway R m) := by
  let := rationalAwayScalarModule R m
  dsimp only
  constructor
  intro q a x
  change rationalAwayScalarAction R m (q • a) x = q • rationalAwayScalarAction R m a x
  simp only [map_smul, LinearMap.smul_apply]

/-- Rational away extraction preserves the existing away residue scalar action. -/
theorem rationalAwayToPrime_scalarAction (m : ℕ) (h : Nat.Coprime p m)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (x : RationalAway R m) :
    rationalAwayToPrime R p m h (rationalAwayScalarAction R m a x) =
      Global.PrimeToProfiniteIntegerRing.rationalToPadic p m h a •
        rationalAwayToPrime R p m h x := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      simp only [rationalAwayScalarAction_tmul, rationalAwayToPrime_tmul,
        Global.PrimeToProfiniteIntegerRing.rationalToPadic_tmul, awayToPrime_smul,
        Rat.cast_mul]
      change ((q : ℚ_[p]) * (r : ℚ_[p])) ⊗ₜ[ℤ_[p]]
          (Global.PrimeToProfiniteIntegerRing.toPadic p m h a • awayToPrime R p m h x) =
        (((q : ℚ_[p]) * (Global.PrimeToProfiniteIntegerRing.toPadic p m h a : ℚ_[p])) *
          (r : ℚ_[p])) ⊗ₜ[ℤ_[p]] awayToPrime R p m h x
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
    | add x y hx hy => simp_all [smul_add]
  | add a b ha hb => simp_all [add_smul]

/-- The existing rational away coordinate map as a semilinear map. -/
def rationalAwayToPrimeSemilinear (m : ℕ) (h : Nat.Coprime p m) :
    let := rationalAwayScalarModule R m
    RationalAway R m →ₛₗ[(Global.PrimeToProfiniteIntegerRing.rationalToPadic p m h).toRingHom]
      TateTwist.Rational R p := by
  let := rationalAwayScalarModule R m
  exact { (rationalAwayToPrime R p m h).toAddHom with
    map_smul' := rationalAwayToPrime_scalarAction R p m h }

@[simp] theorem rationalAwayToPrimeSemilinear_apply
    (m : ℕ) (h : Nat.Coprime p m) (x : RationalAway R m) :
    rationalAwayToPrimeSemilinear R p m h x = rationalAwayToPrime R p m h x := rfl

/-- Restriction of the rational twist commutes with the semilinear projections. -/
theorem rationalAwayToPrimeSemilinear_restrictAway
    (m : ℕ) (h : Nat.Coprime p m) (x : RationalFull R) :
    rationalAwayToPrimeSemilinear R p m h (rationalRestrictAway R m x) =
      rationalFullToPrimeSemilinear R p x :=
  LinearMap.congr_fun (rationalAwayToPrime_restrictAway R p m h) x

variable {R} {S : Type v} [CommRing S]

/-- Ring-induced maps commute with the semilinear rational projections. -/
theorem rationalToPrimeSemilinear_map (hP : ∀ n : ℕ, P (p ^ n))
    (f : R →+* S) (x : Rational R P) :
    rationalToPrimeSemilinear S P p hP (rationalMap P f x) =
      TateTwist.rationalMap p f (rationalToPrimeSemilinear R P p hP x) :=
  LinearMap.congr_fun (rationalToPrime_map P p hP f) x

theorem rationalAwayToPrimeSemilinear_map (m : ℕ) (h : Nat.Coprime p m)
    (f : R →+* S) (x : RationalAway R m) :
    rationalAwayToPrimeSemilinear S p m h (rationalMap _ f x) =
      TateTwist.rationalMap p f (rationalAwayToPrimeSemilinear R p m h x) :=
  LinearMap.congr_fun
    (rationalToPrime_map (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) f) x

end Langlands.TateTwist.Divisibility
