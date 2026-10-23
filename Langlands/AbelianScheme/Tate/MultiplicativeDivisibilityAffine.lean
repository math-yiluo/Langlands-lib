import Langlands.AbelianScheme.Tate.MultiplicativeDivisibility
import Langlands.AbelianScheme.Tate.MultiplicativePrimeAffine
import Langlands.AbelianScheme.Tate.TwistRational

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} {R : CommRingCat.{u}} (f : Spec R ⟶ S) (P : ℕ → Prop)

/-- On an affine test scheme, transport the roots through its canonical section isomorphism. -/
def affineIntegralEquiv :
    Tate.Integral (Gm S).toGrp (Over.mk f) P ≃ₗ[Global.ProfiniteIntegerRing]
      TateTwist.Divisibility.Integral R P :=
  (integralEquiv (Over.mk f) P).trans
    (TateTwist.Divisibility.fullLinearEquiv P (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv)

@[simp] theorem affineIntegralEquiv_apply
    (x : Tate.Integral (Gm S).toGrp (Over.mk f) P) :
    affineIntegralEquiv f P x =
      TateTwist.Divisibility.map P (Scheme.ΓSpecIso R).hom.hom
        (integralEquiv (Over.mk f) P x) := rfl

@[simp] theorem affineIntegralEquiv_symm_apply
    (x : TateTwist.Divisibility.Integral R P) :
    (affineIntegralEquiv f P).symm x =
      (integralEquiv (Over.mk f) P).symm
        (TateTwist.Divisibility.map P (Scheme.ΓSpecIso R).inv.hom x) := rfl

@[simp] theorem evaluation_affineIntegralEquiv (n : Tate.Index P)
    (x : Tate.Integral (Gm S).toGrp (Over.mk f) P) :
    TateTwist.Divisibility.evaluation R P n (affineIntegralEquiv f P x) =
      TateTwist.levelMap (Scheme.ΓSpecIso R).hom.hom n.val
        (levelEquiv (Over.mk f) n.val (Tate.evaluation (Gm S).toGrp (Over.mk f) P n x)) := rfl

theorem continuous_affineIntegralEquiv : Continuous (affineIntegralEquiv f P) :=
  (TateTwist.Divisibility.continuous_map P (Scheme.ΓSpecIso R).hom.hom).comp
    (continuous_integralEquiv (Over.mk f) P)

theorem continuous_affineIntegralEquiv_symm : Continuous (affineIntegralEquiv f P).symm :=
  (continuous_integralEquiv_symm (Over.mk f) P).comp
    (TateTwist.Divisibility.continuous_map P (Scheme.ΓSpecIso R).inv.hom)

/-- The affine comparison with its existing inverse-limit topologies. -/
def affineIntegralContinuousLinearEquiv :
    Tate.Integral (Gm S).toGrp (Over.mk f) P ≃L[Global.ProfiniteIntegerRing]
      TateTwist.Divisibility.Integral R P :=
  { affineIntegralEquiv f P with
    continuous_toFun := continuous_affineIntegralEquiv f P
    continuous_invFun := continuous_affineIntegralEquiv_symm f P }

@[simp] theorem affineIntegralContinuousLinearEquiv_apply
    (x : Tate.Integral (Gm S).toGrp (Over.mk f) P) :
    affineIntegralContinuousLinearEquiv f P x = affineIntegralEquiv f P x := rfl

/-- The affine comparison retaining all positive torsion orders. -/
abbrev affineFullContinuousLinearEquiv :
    Tate.Full (Gm S).toGrp (Over.mk f) ≃L[Global.ProfiniteIntegerRing]
      TateTwist.Divisibility.Full R :=
  affineIntegralContinuousLinearEquiv f (fun _ => True)

variable (m : ℕ)

/-- The affine away comparison is linear over the actual away residue ring. -/
def affineAwayEquiv :
    Tate.Away (Gm S).toGrp (Over.mk f) m ≃ₗ[Global.PrimeToProfiniteIntegerRing m]
      TateTwist.Divisibility.Away R m :=
  (awayEquiv (Over.mk f) m).trans
    (TateTwist.Divisibility.awayLinearEquiv m (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv)

@[simp] theorem affineAwayEquiv_apply (x : Tate.Away (Gm S).toGrp (Over.mk f) m) :
    affineAwayEquiv f m x = affineIntegralEquiv f (fun n => Nat.Coprime n m) x := rfl

@[simp] theorem affineAwayEquiv_symm_apply (x : TateTwist.Divisibility.Away R m) :
    (affineAwayEquiv f m).symm x =
      (affineIntegralEquiv f (fun n => Nat.Coprime n m)).symm x := rfl

/-- The away comparison retains the product-subspace topologies in both directions. -/
def affineAwayContinuousLinearEquiv :
    Tate.Away (Gm S).toGrp (Over.mk f) m ≃L[Global.PrimeToProfiniteIntegerRing m]
      TateTwist.Divisibility.Away R m :=
  { affineAwayEquiv f m with
    continuous_toFun := continuous_affineIntegralEquiv f (fun n => Nat.Coprime n m)
    continuous_invFun := continuous_affineIntegralEquiv_symm f (fun n => Nat.Coprime n m) }

@[simp] theorem affineAwayContinuousLinearEquiv_apply
    (x : Tate.Away (Gm S).toGrp (Over.mk f) m) :
    affineAwayContinuousLinearEquiv f m x = affineAwayEquiv f m x := rfl

/-- Affine specialization commutes with full-to-away restriction. -/
theorem affineAwayContinuousLinearEquiv_restrictAway
    (x : Tate.Full (Gm S).toGrp (Over.mk f)) :
    affineAwayContinuousLinearEquiv f m (Tate.restrictAway (Gm S).toGrp (Over.mk f) m x) =
      TateTwist.Divisibility.restrictAway R m (affineFullContinuousLinearEquiv f x) := rfl

/-- The inverse affine comparison preserves the same restriction square. -/
theorem affineAwayContinuousLinearEquiv_symm_restrictAway
    (x : TateTwist.Divisibility.Full R) :
    (affineAwayContinuousLinearEquiv f m).symm (TateTwist.Divisibility.restrictAway R m x) =
      Tate.restrictAway (Gm S).toGrp (Over.mk f) m
        ((affineFullContinuousLinearEquiv f).symm x) := rfl

variable (p : ℕ) [Fact p.Prime]

/-- Affine specialization commutes with taking the prime-power coordinates. -/
theorem affinePrimeIntegralContinuousLinearEquiv_toPrime (hP : ∀ n : ℕ, P (p ^ n))
    (x : Tate.Integral (Gm S).toGrp (Over.mk f) P) :
    affinePrimeIntegralContinuousLinearEquiv p f
        (Tate.PrimeComparison.toPrime (Gm S).toGrp (Over.mk f) P p hP x) =
      TateTwist.Divisibility.toPrime R P p hP (affineIntegralContinuousLinearEquiv f P x) := rfl

/-- The full affine comparison specializes to the published prime-adic comparison. -/
theorem affinePrimeIntegralContinuousLinearEquiv_fullToPrime
    (x : Tate.Full (Gm S).toGrp (Over.mk f)) :
    affinePrimeIntegralContinuousLinearEquiv p f
        (Tate.PrimeComparison.fullToPrime (Gm S).toGrp (Over.mk f) p x) =
      TateTwist.Divisibility.fullToPrime R p (affineFullContinuousLinearEquiv f x) := rfl

/-- The away affine comparison retains every prime coprime to the modulus. -/
theorem affinePrimeIntegralContinuousLinearEquiv_awayToPrime (h : Nat.Coprime p m)
    (x : Tate.Away (Gm S).toGrp (Over.mk f) m) :
    affinePrimeIntegralContinuousLinearEquiv p f
        (Tate.PrimeComparison.awayToPrime (Gm S).toGrp (Over.mk f) p m h x) =
      TateTwist.Divisibility.awayToPrime R p m h (affineAwayContinuousLinearEquiv f m x) := rfl

end Langlands.GroupScheme.Gm.TateComparison
