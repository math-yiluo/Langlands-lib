import Langlands.AbelianScheme.Tate.MultiplicativeIntegralBaseChange

noncomputable section
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison

universe u
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (T : Over S')
variable (p : ℕ) [Fact p.Prime]

/-- The prime-adic multiplicative comparison under change of base. -/
def primeIntegralBaseChange :
    Tate.PrimeAdic.Integral (Gm S').toGrp T p ≃L[ℤ_[p]]
      Tate.PrimeAdic.Integral (Gm S).toGrp ((Over.map b).obj T) p :=
  (primeIntegralContinuousLinearEquiv T p).trans
    (primeIntegralContinuousLinearEquiv ((Over.map b).obj T) p).symm

@[simp] theorem primeIntegralEquiv_primeIntegralBaseChange
    (x : Tate.PrimeAdic.Integral (Gm S').toGrp T p) :
    primeIntegralEquiv ((Over.map b).obj T) p (primeIntegralBaseChange b T p x) =
      primeIntegralEquiv T p x :=
  (primeIntegralEquiv ((Over.map b).obj T) p).apply_symm_apply _

@[simp] theorem evaluation_primeIntegralBaseChange (n : ℕ)
    (x : Tate.PrimeAdic.Integral (Gm S').toGrp T p) :
    Tate.PrimeAdic.evaluation (Gm S).toGrp ((Over.map b).obj T) p n
        (primeIntegralBaseChange b T p x) =
      levelBaseChange b T (p ^ n)
        (Tate.PrimeAdic.evaluation (Gm S').toGrp T p n x) := rfl

/-- Every coordinate is the actual pullback composite on multiplicative torsion. -/
theorem evaluation_primeIntegralBaseChange_eq_actual (n : ℕ)
    (x : Tate.PrimeAdic.Integral (Gm S').toGrp T p) :
    Tate.PrimeAdic.evaluation (Gm S).toGrp ((Over.map b).obj T) p n
        (primeIntegralBaseChange b T p x) =
      Tate.levelBaseChange b (Gm S).toGrp T (p ^ n)
        (Tate.levelMap T (Gm.baseChangeIso b).inv (p ^ n)
          (Tate.PrimeAdic.evaluation (Gm S').toGrp T p n x)) :=
  levelBaseChange_eq_actual b T (p ^ n) _

/-- Changing base commutes with extracting the retained prime-power coordinates. -/
theorem toPrime_integralBaseChange (P : ℕ → Prop) (hP : ∀ n : ℕ, P (p ^ n))
    (x : Tate.Integral (Gm S').toGrp T P) :
    Tate.PrimeComparison.toPrime (Gm S).toGrp ((Over.map b).obj T) P p hP
        (integralBaseChange b T P x) =
      primeIntegralBaseChange b T p
        (Tate.PrimeComparison.toPrime (Gm S').toGrp T P p hP x) := rfl

/-- The full integral comparison preserves each prime component. -/
theorem fullToPrime_integralBaseChange (x : Tate.Full (Gm S').toGrp T) :
    Tate.PrimeComparison.fullToPrime (Gm S).toGrp ((Over.map b).obj T) p
        (integralBaseChange b T (fun _ => True) x) =
      primeIntegralBaseChange b T p
        (Tate.PrimeComparison.fullToPrime (Gm S').toGrp T p x) := rfl

/-- Away extraction retains the condition that the prime is coprime to the modulus. -/
theorem awayToPrime_awayBaseChange (m : ℕ) (h : Nat.Coprime p m)
    (x : Tate.Away (Gm S').toGrp T m) :
    Tate.PrimeComparison.awayToPrime (Gm S).toGrp ((Over.map b).obj T) p m h
        (awayBaseChange b T m x) =
      primeIntegralBaseChange b T p
        (Tate.PrimeComparison.awayToPrime (Gm S').toGrp T p m h x) := rfl

variable {T}

/-- Base change commutes with actual restriction of prime-power torsion sections. -/
theorem primeIntegralBaseChange_testRestrict {T' : Over S'} (a : T' ⟶ T)
    (x : Tate.PrimeAdic.Integral (Gm S').toGrp T p) :
    primeIntegralBaseChange b T' p (Tate.PrimeAdic.testRestrict (Gm S').toGrp p a x) =
      Tate.PrimeAdic.testRestrict (Gm S).toGrp p ((Over.map b).map a)
        (primeIntegralBaseChange b T p x) := by
  apply (primeIntegralEquiv ((Over.map b).obj T') p).injective
  rw [primeIntegralEquiv_primeIntegralBaseChange, primeIntegralEquiv_testRestrict,
    primeIntegralEquiv_testRestrict, primeIntegralEquiv_primeIntegralBaseChange]
  rfl

variable {R : CommRingCat.{u}} (t : Spec R ⟶ S')

/-- The pointed comparison uses the existing prime-adic modules and topology. -/
abbrev primeIntegralBaseChangeAt :
    Tate.PrimeAdic.Integral (Gm S').toGrp (Over.mk t) p ≃L[ℤ_[p]]
      Tate.PrimeAdic.Integral (Gm S).toGrp (Over.mk (t ≫ b)) p :=
  primeIntegralBaseChange b (Over.mk t) p

/-- The roots in the affine coordinate ring are unchanged by pointed base change. -/
theorem affinePrimeIntegralEquiv_primeIntegralBaseChangeAt
    (x : Tate.PrimeAdic.Integral (Gm S').toGrp (Over.mk t) p) :
    affinePrimeIntegralEquiv p (t ≫ b) (primeIntegralBaseChangeAt b p t x) =
      affinePrimeIntegralEquiv p t x := by
  rw [affinePrimeIntegralEquiv_apply, affinePrimeIntegralEquiv_apply]
  exact congrArg (TateTwist.map p (Scheme.ΓSpecIso R).hom.hom)
    (primeIntegralEquiv_primeIntegralBaseChange b (Over.mk t) p x)

end Langlands.GroupScheme.Gm.TateComparison
