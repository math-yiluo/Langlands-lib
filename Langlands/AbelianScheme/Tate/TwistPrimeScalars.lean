import Langlands.AbelianScheme.Tate.TwistPrimeComparison
import Langlands.Global.ProfiniteIntegerPadicProjection
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

noncomputable section

namespace Langlands.TateTwist.Divisibility
universe u v
variable (R : Type u) [CommRing R] (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- Prime-power extraction respects the canonical projection of full residue scalars. -/
theorem toPrime_smul (hP : ∀ n : ℕ, P (p ^ n))
    (a : Global.ProfiniteIntegerRing) (x : Integral R P) :
    toPrime R P p hP (a • x) =
      Global.ProfiniteIntegerRing.toPadic p a • toPrime R P p hP x := by
  apply Subtype.ext
  funext n
  change GroupScheme.Tate.fullReduction P (primePowerIndex P p hP n) a •
      x.val (primePowerIndex P p hP n) =
    PadicInt.toZModPow n (Global.ProfiniteIntegerRing.toPadic p a) •
      (show Level R (p ^ n) from x.val (primePowerIndex P p hP n))
  rw [Global.ProfiniteIntegerRing.toZModPow_toPadic]
  rfl

/-- The existing coordinate map, bundled over the canonical scalar projection. -/
def toPrimeSemilinear (hP : ∀ n : ℕ, P (p ^ n)) :
    Integral R P →ₛₗ[Global.ProfiniteIntegerRing.toPadic p] TateTwist.Integral R p where
  toAddHom := toPrime R P p hP
  map_smul' := toPrime_smul R P p hP

@[simp] theorem toPrimeSemilinear_apply (hP : ∀ n : ℕ, P (p ^ n)) (x : Integral R P) :
    toPrimeSemilinear R P p hP x = toPrime R P p hP x := rfl

/-- Continuous semilinear prime-power extraction, with the existing limit topologies. -/
def toPrimeContinuousSemilinear (hP : ∀ n : ℕ, P (p ^ n)) :
    Integral R P →SL[Global.ProfiniteIntegerRing.toPadic p] TateTwist.Integral R p where
  toLinearMap := toPrimeSemilinear R P p hP
  cont := continuous_toPrime R P p hP

@[simp] theorem toPrimeContinuousSemilinear_apply
    (hP : ∀ n : ℕ, P (p ^ n)) (x : Integral R P) :
    toPrimeContinuousSemilinear R P p hP x = toPrime R P p hP x := rfl

theorem fullToPrime_smul (a : Global.ProfiniteIntegerRing) (x : Full R) :
    fullToPrime R p (a • x) =
      Global.ProfiniteIntegerRing.toPadic p a • fullToPrime R p x :=
  toPrime_smul R (fun _ => True) p (fun _ => trivial) a x

/-- The full twist projection as a continuous semilinear map. -/
def fullToPrimeContinuousSemilinear :
    Full R →SL[Global.ProfiniteIntegerRing.toPadic p] TateTwist.Integral R p :=
  toPrimeContinuousSemilinear R (fun _ => True) p (fun _ => trivial)

@[simp] theorem fullToPrimeContinuousSemilinear_apply (x : Full R) :
    fullToPrimeContinuousSemilinear R p x = fullToPrime R p x := rfl

/-- Away prime-power extraction respects the canonical away scalar projection. -/
theorem awayToPrime_smul (m : ℕ) (h : Nat.Coprime p m)
    (a : Global.PrimeToProfiniteIntegerRing m) (x : Away R m) :
    awayToPrime R p m h (a • x) =
      Global.PrimeToProfiniteIntegerRing.toPadic p m h a • awayToPrime R p m h x := by
  apply Subtype.ext
  funext n
  change GroupScheme.Tate.awayReduction m
      (primePowerIndex (fun k => Nat.Coprime k m) p (fun k => h.pow_left k) n) a •
      x.val (primePowerIndex (fun k => Nat.Coprime k m) p (fun k => h.pow_left k) n) =
    PadicInt.toZModPow n (Global.PrimeToProfiniteIntegerRing.toPadic p m h a) •
      (show Level R (p ^ n) from
        x.val (primePowerIndex (fun k => Nat.Coprime k m) p (fun k => h.pow_left k) n))
  rw [Global.PrimeToProfiniteIntegerRing.toZModPow_toPadic]
  rfl

/-- The existing away coordinate map, bundled over the away scalar projection. -/
def awayToPrimeSemilinear (m : ℕ) (h : Nat.Coprime p m) :
    Away R m →ₛₗ[Global.PrimeToProfiniteIntegerRing.toPadic p m h]
      TateTwist.Integral R p where
  toAddHom := awayToPrime R p m h
  map_smul' := awayToPrime_smul R p m h

@[simp] theorem awayToPrimeSemilinear_apply (m : ℕ) (h : Nat.Coprime p m) (x : Away R m) :
    awayToPrimeSemilinear R p m h x = awayToPrime R p m h x := rfl

/-- Continuous semilinear extraction from the away twist. -/
def awayToPrimeContinuousSemilinear (m : ℕ) (h : Nat.Coprime p m) :
    Away R m →SL[Global.PrimeToProfiniteIntegerRing.toPadic p m h]
      TateTwist.Integral R p where
  toLinearMap := awayToPrimeSemilinear R p m h
  cont := continuous_awayToPrime R p m h

@[simp] theorem awayToPrimeContinuousSemilinear_apply
    (m : ℕ) (h : Nat.Coprime p m) (x : Away R m) :
    awayToPrimeContinuousSemilinear R p m h x = awayToPrime R p m h x := rfl

theorem awayToPrimeContinuousSemilinear_restrictAway
    (m : ℕ) (h : Nat.Coprime p m) (x : Full R) :
    awayToPrimeContinuousSemilinear R p m h (restrictAway R m x) =
      fullToPrimeContinuousSemilinear R p x := rfl

variable {R} {S : Type v} [CommRing S]

theorem toPrimeContinuousSemilinear_map (hP : ∀ n : ℕ, P (p ^ n))
    (f : R →+* S) (x : Integral R P) :
    toPrimeContinuousSemilinear S P p hP (map P f x) =
      TateTwist.map p f (toPrimeContinuousSemilinear R P p hP x) := rfl

theorem awayToPrimeContinuousSemilinear_map (m : ℕ) (h : Nat.Coprime p m)
    (f : R →+* S) (x : Away R m) :
    awayToPrimeContinuousSemilinear S p m h (map (fun n => Nat.Coprime n m) f x) =
      TateTwist.map p f (awayToPrimeContinuousSemilinear R p m h x) := rfl

variable (R)
attribute [local instance] primeFact

theorem toPrimeProduct_smul_apply (a : Global.ProfiniteIntegerRing) (x : Full R)
    (q : Nat.Primes) :
    toPrimeProduct R (a • x) q =
      Global.ProfiniteIntegerRing.toPadic (q : ℕ) a • toPrimeProduct R x q :=
  fullToPrime_smul R (q : ℕ) a x

theorem toAwayPrimeProduct_smul_apply (m : ℕ)
    (a : Global.PrimeToProfiniteIntegerRing m) (x : Away R m) (q : AwayPrime m) :
    toAwayPrimeProduct R m (a • x) q =
      Global.PrimeToProfiniteIntegerRing.toPadic (q.val : ℕ) m q.property a •
        toAwayPrimeProduct R m x q :=
  awayToPrime_smul R (q.val : ℕ) m q.property a x

end Langlands.TateTwist.Divisibility
