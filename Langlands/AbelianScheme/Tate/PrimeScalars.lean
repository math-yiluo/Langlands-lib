import Langlands.AbelianScheme.Tate.PrimeComparison
import Langlands.AbelianScheme.Tate.Scalars
import Langlands.Global.ProfiniteIntegerPadicProjection
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! # Scalar compatibility of actual Tate prime-coordinate maps -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeComparison

open Langlands.TateTwist.Divisibility (primePowerIndex AwayPrime)

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
variable (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- Selected prime coordinates preserve scalars through the canonical p-adic projection. -/
theorem toPrime_smul (hP : ∀ n : ℕ, P (p ^ n))
    (a : Global.ProfiniteIntegerRing) (x : Integral G T P) :
    toPrime G T P p hP (a • x) =
      Global.ProfiniteIntegerRing.toPadic p a • toPrime G T P p hP x := by
  apply Subtype.ext
  funext n
  let y : Level G T (p ^ n) := x.val (primePowerIndex P p hP n)
  let c : ZMod (p ^ n) := Global.ProfiniteIntegerRing.reduction
    (Global.ProfiniteIntegerRing.primePowerModulus p n) a
  change c • y = PadicInt.toZModPow n (Global.ProfiniteIntegerRing.toPadic p a) • y
  rw [Global.ProfiniteIntegerRing.toZModPow_toPadic]

/-- The selected coordinate map as a semilinear map over actual residue scalars. -/
def toPrimeSemilinear (hP : ∀ n : ℕ, P (p ^ n)) :
    Integral G T P →ₛₗ[Global.ProfiniteIntegerRing.toPadic p] PrimeAdic.Integral G T p where
  toAddHom := toPrime G T P p hP
  map_smul' := toPrime_smul G T P p hP

/-- The same coordinate map with its existing continuity proof. -/
def toPrimeContinuousSemilinear (hP : ∀ n : ℕ, P (p ^ n)) :
    Integral G T P →SL[Global.ProfiniteIntegerRing.toPadic p] PrimeAdic.Integral G T p where
  toLinearMap := toPrimeSemilinear G T P p hP
  cont := continuous_toPrime G T P p hP

/-- Full prime coordinates use the canonical full scalar projection. -/
theorem fullToPrime_smul (a : Global.ProfiniteIntegerRing) (x : Full G T) :
    fullToPrime G T p (a • x) =
      Global.ProfiniteIntegerRing.toPadic p a • fullToPrime G T p x :=
  toPrime_smul G T (fun _ => True) p (fun _ => trivial) a x

/-- Full prime coordinates as a continuous semilinear map. -/
def fullToPrimeContinuousSemilinear :
    Full G T →SL[Global.ProfiniteIntegerRing.toPadic p] PrimeAdic.Integral G T p :=
  toPrimeContinuousSemilinear G T (fun _ => True) p (fun _ => trivial)

/-- Away prime coordinates use the canonical away scalar projection. -/
theorem awayToPrime_smul (m : ℕ) (h : Nat.Coprime p m)
    (a : Global.PrimeToProfiniteIntegerRing m) (x : Away G T m) :
    awayToPrime G T p m h (a • x) =
      Global.PrimeToProfiniteIntegerRing.toPadic p m h a • awayToPrime G T p m h x := by
  apply Subtype.ext
  funext n
  let y : Level G T (p ^ n) := x.val
    (primePowerIndex (fun k => Nat.Coprime k m) p (fun n => h.pow_left n) n)
  let c : ZMod (p ^ n) := Global.PrimeToProfiniteIntegerRing.reduction
    (Global.PrimeToProfiniteIntegerRing.primePowerModulus p m h n) a
  change c • y = PadicInt.toZModPow n (Global.PrimeToProfiniteIntegerRing.toPadic p m h a) • y
  rw [Global.PrimeToProfiniteIntegerRing.toZModPow_toPadic]

/-- Away coordinates as a semilinear map over away residue scalars. -/
def awayToPrimeSemilinear (m : ℕ) (h : Nat.Coprime p m) :
    Away G T m →ₛₗ[Global.PrimeToProfiniteIntegerRing.toPadic p m h]
      PrimeAdic.Integral G T p where
  toAddHom := awayToPrime G T p m h
  map_smul' := awayToPrime_smul G T p m h

/-- Away coordinates with their existing continuity proof. -/
def awayToPrimeContinuousSemilinear (m : ℕ) (h : Nat.Coprime p m) :
    Away G T m →SL[Global.PrimeToProfiniteIntegerRing.toPadic p m h]
      PrimeAdic.Integral G T p where
  toLinearMap := awayToPrimeSemilinear G T p m h
  cont := continuous_awayToPrime G T p m h

/-- Coordinate scalar compatibility after restricting both the module and the scalar. -/
theorem awayToPrime_restrictAway_smul (m : ℕ) (h : Nat.Coprime p m)
    (a : Global.ProfiniteIntegerRing) (x : Full G T) :
    awayToPrime G T p m h (restrictAway G T m (a • x)) =
      Global.ProfiniteIntegerRing.toPadic p a • fullToPrime G T p x := by
  rw [awayToPrime_restrictAway, fullToPrime_smul]

attribute [local instance] primeFact

/-- The full product map preserves scalars coordinatewise. -/
theorem toPrimeProduct_smul (a : Global.ProfiniteIntegerRing) (x : Full G T)
    (q : Nat.Primes) :
    toPrimeProduct G T (a • x) q =
      Global.ProfiniteIntegerRing.toPadic (q : ℕ) a • toPrimeProduct G T x q :=
  fullToPrime_smul G T (q : ℕ) a x

/-- The away product map preserves away scalars coordinatewise. -/
theorem toAwayPrimeProduct_smul (m : ℕ) (a : Global.PrimeToProfiniteIntegerRing m)
    (x : Away G T m) (q : AwayPrime m) :
    toAwayPrimeProduct G T m (a • x) q =
      Global.PrimeToProfiniteIntegerRing.toPadic (q.val : ℕ) m q.property a •
        toAwayPrimeProduct G T m x q :=
  awayToPrime_smul G T (q.val : ℕ) m q.property a x

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)
variable (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- Actual selected abelian-scheme Tate coordinates as a continuous semilinear map. -/
abbrev toPrimeContinuousSemilinear (hP : ∀ n : ℕ, P (p ^ n)) :
    Integral A T P →SL[Global.ProfiniteIntegerRing.toPadic p] PrimeAdic.Integral A T p :=
  GroupScheme.Tate.PrimeComparison.toPrimeContinuousSemilinear A.toGrp T P p hP

/-- Actual full abelian-scheme Tate coordinates as a continuous semilinear map. -/
abbrev fullToPrimeContinuousSemilinear :
    Full A T →SL[Global.ProfiniteIntegerRing.toPadic p] PrimeAdic.Integral A T p :=
  GroupScheme.Tate.PrimeComparison.fullToPrimeContinuousSemilinear A.toGrp T p

/-- Actual away abelian-scheme Tate coordinates as a continuous semilinear map. -/
abbrev awayToPrimeContinuousSemilinear (m : ℕ) (h : Nat.Coprime p m) :
    Away A T m →SL[Global.PrimeToProfiniteIntegerRing.toPadic p m h]
      PrimeAdic.Integral A T p :=
  GroupScheme.Tate.PrimeComparison.awayToPrimeContinuousSemilinear A.toGrp T p m h

end Langlands.AbelianScheme.Tate.PrimeComparison
