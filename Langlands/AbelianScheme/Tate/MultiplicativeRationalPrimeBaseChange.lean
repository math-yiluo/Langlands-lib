import Langlands.AbelianScheme.Tate.MultiplicativePrimeBaseChange
import Langlands.AbelianScheme.Tate.MultiplicativeRationalBaseChange
import Langlands.AbelianScheme.Tate.RationalPrimeScalars
import Langlands.AbelianScheme.Tate.TwistRationalPrime

noncomputable section
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison

universe u
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (T : Over S')
variable (p : ℕ) [Fact p.Prime]

/-- Extend the actual integral prime-adic multiplicative comparison to the p-adic field. -/
def primeRationalBaseChange :
    Tate.PrimeAdic.Rational (Gm S').toGrp T p ≃ₗ[ℚ_[p]]
      Tate.PrimeAdic.Rational (Gm S).toGrp ((Over.map b).obj T) p :=
  (primeIntegralBaseChange b T p).toLinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _

@[simp] theorem primeRationalBaseChange_tmul (q : ℚ_[p])
    (x : Tate.PrimeAdic.Integral (Gm S').toGrp T p) :
    primeRationalBaseChange b T p (q ⊗ₜ[ℤ_[p]] x) =
      q ⊗ₜ[ℤ_[p]] primeIntegralBaseChange b T p x := rfl

@[simp] theorem primeRationalBaseChange_toRational
    (x : Tate.PrimeAdic.Integral (Gm S').toGrp T p) :
    primeRationalBaseChange b T p (Tate.PrimeAdic.toRational (Gm S').toGrp T p x) =
      Tate.PrimeAdic.toRational (Gm S).toGrp ((Over.map b).obj T) p
        (primeIntegralBaseChange b T p x) := rfl

/-- The rational root family is unchanged under this base change. -/
theorem primeRationalEquiv_primeRationalBaseChange
    (x : Tate.PrimeAdic.Rational (Gm S').toGrp T p) :
    primeRationalEquiv ((Over.map b).obj T) p (primeRationalBaseChange b T p x) =
      primeRationalEquiv T p x := by
  have heq : (primeRationalEquiv ((Over.map b).obj T) p).toLinearMap.comp
      (primeRationalBaseChange b T p).toLinearMap = (primeRationalEquiv T p).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q y
    change q ⊗ₜ[ℤ_[p]] primeIntegralEquiv ((Over.map b).obj T) p
      (primeIntegralBaseChange b T p y) = q ⊗ₜ[ℤ_[p]] primeIntegralEquiv T p y
    rw [primeIntegralEquiv_primeIntegralBaseChange]
  exact LinearMap.congr_fun heq x

/-- Extraction of retained prime-power coordinates commutes with rational base change. -/
theorem rationalToPrime_rationalBaseChange (P : ℕ → Prop) (hP : ∀ n : ℕ, P (p ^ n))
    (x : Tate.Rational (Gm S').toGrp T P) :
    Tate.PrimeComparison.rationalToPrime (Gm S).toGrp ((Over.map b).obj T) P p hP
        (rationalBaseChange b T P x) =
      primeRationalBaseChange b T p
        (Tate.PrimeComparison.rationalToPrime (Gm S').toGrp T P p hP x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalBaseChange_tmul, Tate.PrimeComparison.rationalToPrime_tmul,
      primeRationalBaseChange_tmul, toPrime_integralBaseChange]
    rfl
  | add x y hx hy => simp_all

/-- The semilinear extraction has the same underlying compatibility square. -/
theorem rationalToPrimeSemilinear_rationalBaseChange
    (P : ℕ → Prop) (hP : ∀ n : ℕ, P (p ^ n))
    (x : Tate.Rational (Gm S').toGrp T P) :
    Tate.PrimeComparison.rationalToPrimeSemilinear (Gm S).toGrp
        ((Over.map b).obj T) P p hP (rationalBaseChange b T P x) =
      primeRationalBaseChange b T p
        (Tate.PrimeComparison.rationalToPrimeSemilinear (Gm S').toGrp T P p hP x) :=
  rationalToPrime_rationalBaseChange b T p P hP x

/-- The full rational prime-coordinate square. -/
theorem rationalFullToPrime_rationalBaseChange (x : Tate.RationalFull (Gm S').toGrp T) :
    Tate.PrimeComparison.rationalFullToPrime (Gm S).toGrp ((Over.map b).obj T) p
        (rationalBaseChange b T (fun _ => True) x) =
      primeRationalBaseChange b T p
        (Tate.PrimeComparison.rationalFullToPrime (Gm S').toGrp T p x) :=
  rationalToPrime_rationalBaseChange b T p (fun _ => True) (fun _ => trivial) x

/-- The away square retains coprimality of the prime with the excluded modulus. -/
theorem rationalAwayToPrime_rationalBaseChange (m : ℕ) (h : Nat.Coprime p m)
    (x : Tate.RationalAway (Gm S').toGrp T m) :
    Tate.PrimeComparison.rationalAwayToPrime (Gm S).toGrp ((Over.map b).obj T) p m h
        (rationalBaseChange b T (fun n => Nat.Coprime n m) x) =
      primeRationalBaseChange b T p
        (Tate.PrimeComparison.rationalAwayToPrime (Gm S').toGrp T p m h x) :=
  rationalToPrime_rationalBaseChange b T p (fun n => Nat.Coprime n m)
    (fun n => h.pow_left n) x

/-- The away semilinear coordinate map preserves the same square. -/
theorem rationalAwayToPrimeSemilinear_rationalBaseChange (m : ℕ) (h : Nat.Coprime p m)
    (x : Tate.RationalAway (Gm S').toGrp T m) :
    Tate.PrimeComparison.rationalAwayToPrimeSemilinear (Gm S).toGrp
        ((Over.map b).obj T) p m h (rationalBaseChange b T (fun n => Nat.Coprime n m) x) =
      primeRationalBaseChange b T p
        (Tate.PrimeComparison.rationalAwayToPrimeSemilinear (Gm S').toGrp T p m h x) :=
  rationalAwayToPrime_rationalBaseChange b T p m h x

variable {T}

/-- Rational prime-adic base change commutes with actual test-scheme restriction. -/
theorem primeRationalBaseChange_testRestrict {T' : Over S'} (a : T' ⟶ T)
    (x : Tate.PrimeAdic.Rational (Gm S').toGrp T p) :
    primeRationalBaseChange b T' p (Tate.PrimeAdic.rationalTestRestrict (Gm S').toGrp p a x) =
      Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p ((Over.map b).map a)
        (primeRationalBaseChange b T p x) := by
  have heq : (primeRationalBaseChange b T' p).toLinearMap.comp
      (Tate.PrimeAdic.rationalTestRestrict (Gm S').toGrp p a) =
      (Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p ((Over.map b).map a)).comp
        (primeRationalBaseChange b T p).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q y
    change q ⊗ₜ[ℤ_[p]] primeIntegralBaseChange b T' p
      (Tate.PrimeAdic.testRestrict (Gm S').toGrp p a y) =
      q ⊗ₜ[ℤ_[p]] Tate.PrimeAdic.testRestrict (Gm S).toGrp p ((Over.map b).map a)
        (primeIntegralBaseChange b T p y)
    rw [primeIntegralBaseChange_testRestrict]
  exact LinearMap.congr_fun heq x

variable {R : CommRingCat.{u}} (t : Spec R ⟶ S')

/-- Pointed algebraic comparison on the existing rational prime-adic Tate modules. -/
abbrev primeRationalBaseChangeAt :
    Tate.PrimeAdic.Rational (Gm S').toGrp (Over.mk t) p ≃ₗ[ℚ_[p]]
      Tate.PrimeAdic.Rational (Gm S).toGrp (Over.mk (t ≫ b)) p :=
  primeRationalBaseChange b (Over.mk t) p

/-- Affine rational roots are unchanged when the point is composed with the base map. -/
theorem affinePrimeRationalEquiv_primeRationalBaseChangeAt
    (x : Tate.PrimeAdic.Rational (Gm S').toGrp (Over.mk t) p) :
    affinePrimeRationalEquiv p (t ≫ b) (primeRationalBaseChangeAt b p t x) =
      affinePrimeRationalEquiv p t x := by
  have heq : (affinePrimeRationalEquiv p (t ≫ b)).toLinearMap.comp
      (primeRationalBaseChangeAt b p t).toLinearMap =
      (affinePrimeRationalEquiv p t).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q y
    change q ⊗ₜ[ℤ_[p]] affinePrimeIntegralEquiv p (t ≫ b)
      (primeIntegralBaseChangeAt b p t y) = q ⊗ₜ[ℤ_[p]] affinePrimeIntegralEquiv p t y
    rw [affinePrimeIntegralEquiv_primeIntegralBaseChangeAt]
  exact LinearMap.congr_fun heq x

end Langlands.GroupScheme.Gm.TateComparison
