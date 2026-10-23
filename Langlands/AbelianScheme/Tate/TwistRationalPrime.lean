import Langlands.AbelianScheme.Tate.TwistRational
import Langlands.AbelianScheme.Tate.TwistPrimeComparison

noncomputable section
open scoped TensorProduct

namespace Langlands.TateTwist
universe u v
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]

instance rationalRatModule : Module ℚ (Rational R p) :=
  inferInstanceAs (Module ℚ (ℚ_[p] ⊗[ℤ_[p]] Integral R p))

instance rationalPadicIntModule : Module ℤ_[p] (Rational R p) :=
  inferInstanceAs (Module ℤ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral R p))

instance rationalRatScalarTower : IsScalarTower ℚ ℚ_[p] (Rational R p) :=
  inferInstanceAs (IsScalarTower ℚ ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral R p))

instance rationalPadicIntScalarTower : IsScalarTower ℤ_[p] ℚ_[p] (Rational R p) :=
  inferInstanceAs (IsScalarTower ℤ_[p] ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral R p))

/-- The canonical map from the integral prime-adic twist to its rationalization. -/
def toRational : Integral R p →ₗ[ℤ_[p]] Rational R p :=
  TensorProduct.mk ℤ_[p] ℚ_[p] (Integral R p) 1

@[simp] theorem toRational_apply (x : Integral R p) :
    toRational R p x = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x := rfl

end Langlands.TateTwist

namespace Langlands.TateTwist.Divisibility
universe u v
variable (R : Type u) [CommRing R] (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- The canonical rational map to a prime-adic rational twist. -/
def rationalToPrime (hP : ∀ n : ℕ, P (p ^ n)) :
    Rational R P →ₗ[ℚ] TateTwist.Rational R p :=
  TensorProduct.AlgebraTensorModule.lift {
    toFun q := q • ((TateTwist.toRational R p).restrictScalars ℤ).comp
      (toPrime R P p hP).toIntLinearMap
    map_add' q r := add_smul q r _
    map_smul' q r := mul_smul q r _ }

@[simp] theorem rationalToPrime_tmul (hP : ∀ n : ℕ, P (p ^ n))
    (q : ℚ) (x : Integral R P) :
    rationalToPrime R P p hP (q ⊗ₜ[ℤ] x) =
      (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] toPrime R P p hP x := by
  change q • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] toPrime R P p hP x) = _
  rw [TensorProduct.smul_tmul']
  simp

/-- The pure-tensor formula determines the rational extraction map. -/
theorem rationalToPrime_unique (hP : ∀ n : ℕ, P (p ^ n))
    (g : Rational R P →ₗ[ℚ] TateTwist.Rational R p)
    (hg : ∀ (q : ℚ) (x : Integral R P),
      g (q ⊗ₜ[ℤ] x) = (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] toPrime R P p hP x) :
    g = rationalToPrime R P p hP := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  rw [hg, rationalToPrime_tmul]

@[simp] theorem rationalToPrime_toRational (hP : ∀ n : ℕ, P (p ^ n))
    (x : Integral R P) :
    rationalToPrime R P p hP (toRational R P x) =
      TateTwist.toRational R p (toPrime R P p hP x) := by
  change rationalToPrime R P p hP ((1 : ℚ) ⊗ₜ[ℤ] x) =
    (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] toPrime R P p hP x
  rw [rationalToPrime_tmul, Rat.cast_one]

/-- Rational extraction from the full roots-of-unity twist. -/
def rationalFullToPrime : RationalFull R →ₗ[ℚ] TateTwist.Rational R p :=
  rationalToPrime R (fun _ => True) p (fun _ => trivial)

@[simp] theorem rationalFullToPrime_tmul (q : ℚ) (x : Full R) :
    rationalFullToPrime R p (q ⊗ₜ[ℤ] x) =
      (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] fullToPrime R p x :=
  rationalToPrime_tmul R (fun _ => True) p (fun _ => trivial) q x

/-- Rational extraction at a prime retained by the away system. -/
def rationalAwayToPrime (m : ℕ) (h : Nat.Coprime p m) :
    RationalAway R m →ₗ[ℚ] TateTwist.Rational R p :=
  rationalToPrime R (fun n => Nat.Coprime n m) p (fun n => h.pow_left n)

@[simp] theorem rationalAwayToPrime_tmul (m : ℕ) (h : Nat.Coprime p m)
    (q : ℚ) (x : Away R m) :
    rationalAwayToPrime R p m h (q ⊗ₜ[ℤ] x) =
      (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] awayToPrime R p m h x :=
  rationalToPrime_tmul R (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) q x

theorem rationalAwayToPrime_restrictAway (m : ℕ) (h : Nat.Coprime p m) :
    (rationalAwayToPrime R p m h).comp (rationalRestrictAway R m) =
      rationalFullToPrime R p := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp only [LinearMap.comp_apply, rationalRestrictAway_tmul,
    rationalAwayToPrime_tmul, rationalFullToPrime_tmul, awayToPrime_restrictAway]
  rfl

variable {R} {S : Type v} [CommRing S]

theorem rationalToPrime_map (hP : ∀ n : ℕ, P (p ^ n)) (f : R →+* S) :
    (rationalToPrime S P p hP).comp (rationalMap P f) =
      ((TateTwist.rationalMap p f).restrictScalars ℚ).comp
        (rationalToPrime R P p hP) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  change rationalToPrime S P p hP (rationalMap P f (q ⊗ₜ[ℤ] x)) =
    TateTwist.rationalMap p f (rationalToPrime R P p hP (q ⊗ₜ[ℤ] x))
  simp only [rationalMap_tmul, rationalToPrime_tmul,
    TateTwist.rationalMap_tmul, toPrime_map]
  rfl

end Langlands.TateTwist.Divisibility
