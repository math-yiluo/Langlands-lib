import Langlands.AbelianScheme.Tate.IntegralBaseChange
import Langlands.AbelianScheme.Tate.MultiplicativeAffineTestScheme

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison

universe u
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (T : Over S')

/-- Actual pullback of Gm torsion preserves its root coordinate. -/
theorem levelEquiv_actualBaseChange (n : ℕ)
    (x : Tate.Level (Gm S').toGrp T n) :
    levelEquiv ((Over.map b).obj T) n
        (Tate.levelBaseChange b (Gm S).toGrp T n
          (Tate.levelMap T (Gm.baseChangeIso b).inv n x)) =
      levelEquiv T n x := by
  apply TateTwist.toUnit_injective
  exact Gm.baseChangeUnitsEquiv_baseChangeIso_inv b T (Additive.toMul x).val

/-- The root-coordinate equivalence for base change, identified below with pullback. -/
def levelBaseChange (n : ℕ) :
    Tate.Level (Gm S').toGrp T n ≃ₗ[ZMod n]
      Tate.Level (Gm S).toGrp ((Over.map b).obj T) n :=
  (levelLinearEquiv T n).trans (levelLinearEquiv ((Over.map b).obj T) n).symm

/-- The equivalence is the actual canonical Gm isomorphism followed by torsion pullback. -/
theorem levelBaseChange_eq_actual (n : ℕ)
    (x : Tate.Level (Gm S').toGrp T n) :
    levelBaseChange b T n x =
      Tate.levelBaseChange b (Gm S).toGrp T n
        (Tate.levelMap T (Gm.baseChangeIso b).inv n x) := by
  apply (levelEquiv ((Over.map b).obj T) n).injective
  change (levelEquiv ((Over.map b).obj T) n)
      ((levelEquiv ((Over.map b).obj T) n).symm (levelEquiv T n x)) = _
  rw [AddEquiv.apply_symm_apply]
  exact (levelEquiv_actualBaseChange b T n x).symm

@[simp] theorem levelEquiv_levelBaseChange (n : ℕ)
    (x : Tate.Level (Gm S').toGrp T n) :
    levelEquiv ((Over.map b).obj T) n (levelBaseChange b T n x) =
      levelEquiv T n x :=
  (levelEquiv ((Over.map b).obj T) n).apply_symm_apply _

theorem levelBaseChange_transition {n m : ℕ} (h : n ∣ m)
    (x : Tate.Level (Gm S').toGrp T m) :
    levelBaseChange b T n (Tate.transition (Gm S').toGrp T h x) =
      Tate.transition (Gm S).toGrp ((Over.map b).obj T) h (levelBaseChange b T m x) := by
  apply (levelEquiv ((Over.map b).obj T) n).injective
  rw [levelEquiv_levelBaseChange, levelEquiv_transition, levelEquiv_transition,
    levelEquiv_levelBaseChange]
  rfl

/-- Integral multiplicative base change with its residue scalars and limit topology. -/
def integralBaseChange (P : ℕ → Prop) :
    Tate.Integral (Gm S').toGrp T P ≃L[Global.ProfiniteIntegerRing]
      Tate.Integral (Gm S).toGrp ((Over.map b).obj T) P :=
  (integralContinuousLinearEquiv T P).trans
    (integralContinuousLinearEquiv ((Over.map b).obj T) P).symm

@[simp] theorem integralEquiv_integralBaseChange (P : ℕ → Prop)
    (x : Tate.Integral (Gm S').toGrp T P) :
    integralEquiv ((Over.map b).obj T) P (integralBaseChange b T P x) =
      integralEquiv T P x :=
  (integralEquiv ((Over.map b).obj T) P).apply_symm_apply _

@[simp] theorem evaluation_integralBaseChange (P : ℕ → Prop) (n : Tate.Index P)
    (x : Tate.Integral (Gm S').toGrp T P) :
    Tate.evaluation (Gm S).toGrp ((Over.map b).obj T) P n
        (integralBaseChange b T P x) =
      levelBaseChange b T n.val (Tate.evaluation (Gm S').toGrp T P n x) := rfl

/-- The integral equivalence is induced by the actual group-scheme pullback. -/
theorem integralBaseChange_eq_actual (P : ℕ → Prop)
    (x : Tate.Integral (Gm S').toGrp T P) :
    integralBaseChange b T P x =
      Tate.integralBaseChange b (Gm S).toGrp T P
        (Tate.map T P (Gm.baseChangeIso b).inv x) := by
  apply Subtype.ext
  funext n
  exact levelBaseChange_eq_actual b T n.val (x.val n)

/-- The same comparison over the away residue ring. -/
def awayBaseChange (m : ℕ) :
    Tate.Away (Gm S').toGrp T m ≃L[Global.PrimeToProfiniteIntegerRing m]
      Tate.Away (Gm S).toGrp ((Over.map b).obj T) m :=
  (awayContinuousLinearEquiv T m).trans
    (awayContinuousLinearEquiv ((Over.map b).obj T) m).symm

@[simp] theorem awayBaseChange_apply (m : ℕ) (x : Tate.Away (Gm S').toGrp T m) :
    awayBaseChange b T m x = integralBaseChange b T (fun n => Nat.Coprime n m) x := rfl

/-- Changing the base preserves restriction from all orders to the retained orders. -/
theorem integralBaseChange_restrictAway (m : ℕ) (x : Tate.Full (Gm S').toGrp T) :
    awayBaseChange b T m (Tate.restrictAway (Gm S').toGrp T m x) =
      Tate.restrictAway (Gm S).toGrp ((Over.map b).obj T) m
        (integralBaseChange b T (fun _ => True) x) := rfl

variable {T}

/-- The comparison is natural for actual morphisms of test schemes. -/
theorem integralBaseChange_testRestrict {T' : Over S'} (P : ℕ → Prop) (a : T' ⟶ T)
    (x : Tate.Integral (Gm S').toGrp T P) :
    integralBaseChange b T' P (Tate.testRestrict (Gm S').toGrp P a x) =
      Tate.testRestrict (Gm S).toGrp P ((Over.map b).map a)
        (integralBaseChange b T P x) := by
  apply (integralEquiv ((Over.map b).obj T') P).injective
  rw [integralEquiv_integralBaseChange, integralEquiv_testRestrict,
    integralEquiv_testRestrict, integralEquiv_integralBaseChange]
  rfl

variable {R : CommRingCat.{u}} (t : Spec R ⟶ S')

/-- Affine root coordinates are unchanged by pointed base change. -/
theorem affineIntegralEquiv_integralBaseChange (P : ℕ → Prop)
    (x : Tate.Integral (Gm S').toGrp (Over.mk t) P) :
    affineIntegralEquiv (t ≫ b) P (integralBaseChange b (Over.mk t) P x) =
      affineIntegralEquiv t P x := by
  rw [affineIntegralEquiv_apply, affineIntegralEquiv_apply]
  exact congrArg (TateTwist.Divisibility.map P (Scheme.ΓSpecIso R).hom.hom)
    (integralEquiv_integralBaseChange b (Over.mk t) P x)

/-- Pointed full base change is a continuous residue-linear equivalence. -/
abbrev fullBaseChangeAt :
    Tate.Full (Gm S').toGrp (Over.mk t) ≃L[Global.ProfiniteIntegerRing]
      Tate.Full (Gm S).toGrp (Over.mk (t ≫ b)) :=
  integralBaseChange b (Over.mk t) (fun _ => True)

/-- Pointed away base change uses the actual away residue ring. -/
abbrev awayBaseChangeAt (m : ℕ) :
    Tate.Away (Gm S').toGrp (Over.mk t) m ≃L[Global.PrimeToProfiniteIntegerRing m]
      Tate.Away (Gm S).toGrp (Over.mk (t ≫ b)) m :=
  awayBaseChange b (Over.mk t) m

theorem affineAwayEquiv_awayBaseChangeAt (m : ℕ)
    (x : Tate.Away (Gm S').toGrp (Over.mk t) m) :
    affineAwayEquiv (t ≫ b) m (awayBaseChangeAt b t m x) =
      affineAwayEquiv t m x :=
  affineIntegralEquiv_integralBaseChange b t (fun n => Nat.Coprime n m) x

end Langlands.GroupScheme.Gm.TateComparison
