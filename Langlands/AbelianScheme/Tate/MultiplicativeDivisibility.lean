import Langlands.AbelianScheme.Tate.MultiplicativePrime
import Langlands.AbelianScheme.Tate.PrimeComparison

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} (T : Over S) (P : ℕ → Prop)

/-- The actual selected torsion limit of Gm is the selected roots-of-unity limit. -/
def integralEquiv :
    Tate.Integral (Gm S).toGrp T P ≃ₗ[Global.ProfiniteIntegerRing]
      TateTwist.Divisibility.Integral Γ(T.left, ⊤) P where
  toFun x := ⟨fun n => levelEquiv T n.val (x.val n), by
    intro n m h
    rw [← levelEquiv_transition, x.property n m h]⟩
  invFun x := ⟨fun n => (levelEquiv T n.val).symm (x.val n), by
    intro n m h
    apply (levelEquiv T n.val).injective
    rw [levelEquiv_transition, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact x.property n m h⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (levelEquiv T n.val).symm_apply_apply (x.val n)
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (levelEquiv T n.val).apply_symm_apply (x.val n)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (levelEquiv T n.val) (x.val n) (y.val n)
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact ZMod.map_smul (levelEquiv T n.val).toAddMonoidHom
      (Tate.fullReduction P n a) (x.val n)

@[simp] theorem evaluation_integralEquiv (n : Tate.Index P)
    (x : Tate.Integral (Gm S).toGrp T P) :
    TateTwist.Divisibility.evaluation Γ(T.left, ⊤) P n (integralEquiv T P x) =
      levelEquiv T n.val (Tate.evaluation (Gm S).toGrp T P n x) := rfl

@[simp] theorem evaluation_integralEquiv_symm (n : Tate.Index P)
    (x : TateTwist.Divisibility.Integral Γ(T.left, ⊤) P) :
    Tate.evaluation (Gm S).toGrp T P n ((integralEquiv T P).symm x) =
      (levelEquiv T n.val).symm (TateTwist.Divisibility.evaluation Γ(T.left, ⊤) P n x) := rfl

theorem continuous_integralEquiv : Continuous (integralEquiv T P) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := levelEquiv T n.val)).comp
    (Tate.continuous_evaluation (Gm S).toGrp T P n)

theorem continuous_integralEquiv_symm : Continuous (integralEquiv T P).symm := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := (levelEquiv T n.val).symm)).comp
    (TateTwist.Divisibility.continuous_evaluation Γ(T.left, ⊤) P n)

/-- The selected comparison retains the existing residue scalars and limit topologies. -/
def integralContinuousLinearEquiv :
    Tate.Integral (Gm S).toGrp T P ≃L[Global.ProfiniteIntegerRing]
      TateTwist.Divisibility.Integral Γ(T.left, ⊤) P :=
  { integralEquiv T P with
    continuous_toFun := continuous_integralEquiv T P
    continuous_invFun := continuous_integralEquiv_symm T P }

@[simp] theorem integralContinuousLinearEquiv_apply
    (x : Tate.Integral (Gm S).toGrp T P) :
    integralContinuousLinearEquiv T P x = integralEquiv T P x := rfl

/-- The full integral comparison. -/
abbrev fullContinuousLinearEquiv :
    Tate.Full (Gm S).toGrp T ≃L[Global.ProfiniteIntegerRing]
      TateTwist.Divisibility.Full Γ(T.left, ⊤) :=
  integralContinuousLinearEquiv T (fun _ => True)

variable (m : ℕ)

/-- The away comparison over the actual away residue scalar ring. -/
def awayEquiv :
    Tate.Away (Gm S).toGrp T m ≃ₗ[Global.PrimeToProfiniteIntegerRing m]
      TateTwist.Divisibility.Away Γ(T.left, ⊤) m :=
  { (integralEquiv T (fun n => Nat.Coprime n m)).toAddEquiv with
    map_smul' := by
      intro a x
      apply Subtype.ext
      funext n
      exact ZMod.map_smul (levelEquiv T n.val).toAddMonoidHom
        (Tate.awayReduction m n a) (x.val n) }

@[simp] theorem awayEquiv_apply (x : Tate.Away (Gm S).toGrp T m) :
    awayEquiv T m x = integralEquiv T (fun n => Nat.Coprime n m) x := rfl

/-- The away comparison has continuous forward and inverse maps. -/
def awayContinuousLinearEquiv :
    Tate.Away (Gm S).toGrp T m ≃L[Global.PrimeToProfiniteIntegerRing m]
      TateTwist.Divisibility.Away Γ(T.left, ⊤) m :=
  { awayEquiv T m with
    continuous_toFun := continuous_integralEquiv T (fun n => Nat.Coprime n m)
    continuous_invFun := continuous_integralEquiv_symm T (fun n => Nat.Coprime n m) }

@[simp] theorem awayContinuousLinearEquiv_apply (x : Tate.Away (Gm S).toGrp T m) :
    awayContinuousLinearEquiv T m x = integralEquiv T (fun n => Nat.Coprime n m) x := rfl

/-- The full-to-away restriction commutes with the geometric comparison. -/
theorem awayContinuousLinearEquiv_restrictAway (x : Tate.Full (Gm S).toGrp T) :
    awayContinuousLinearEquiv T m (Tate.restrictAway (Gm S).toGrp T m x) =
      TateTwist.Divisibility.restrictAway Γ(T.left, ⊤) m (fullContinuousLinearEquiv T x) := rfl

/-- The inverse comparison commutes with the same restriction. -/
theorem awayContinuousLinearEquiv_symm_restrictAway
    (x : TateTwist.Divisibility.Full Γ(T.left, ⊤)) :
    (awayContinuousLinearEquiv T m).symm
        (TateTwist.Divisibility.restrictAway Γ(T.left, ⊤) m x) =
      Tate.restrictAway (Gm S).toGrp T m ((fullContinuousLinearEquiv T).symm x) := rfl

variable (p : ℕ) [Fact p.Prime]

/-- Taking prime-power coordinates commutes with the selected comparison. -/
theorem primeIntegralContinuousLinearEquiv_toPrime (hP : ∀ n : ℕ, P (p ^ n))
    (x : Tate.Integral (Gm S).toGrp T P) :
    primeIntegralContinuousLinearEquiv T p
        (Tate.PrimeComparison.toPrime (Gm S).toGrp T P p hP x) =
      TateTwist.Divisibility.toPrime Γ(T.left, ⊤) P p hP
        (integralContinuousLinearEquiv T P x) := rfl

/-- Prime extraction from the full module is the published prime-adic comparison. -/
theorem primeIntegralContinuousLinearEquiv_fullToPrime
    (x : Tate.Full (Gm S).toGrp T) :
    primeIntegralContinuousLinearEquiv T p
        (Tate.PrimeComparison.fullToPrime (Gm S).toGrp T p x) =
      TateTwist.Divisibility.fullToPrime Γ(T.left, ⊤) p (fullContinuousLinearEquiv T x) := rfl

/-- Prime extraction from an away module commutes when the prime is retained. -/
theorem primeIntegralContinuousLinearEquiv_awayToPrime (h : Nat.Coprime p m)
    (x : Tate.Away (Gm S).toGrp T m) :
    primeIntegralContinuousLinearEquiv T p
        (Tate.PrimeComparison.awayToPrime (Gm S).toGrp T p m h x) =
      TateTwist.Divisibility.awayToPrime Γ(T.left, ⊤) p m h
        (awayContinuousLinearEquiv T m x) := rfl

end Langlands.GroupScheme.Gm.TateComparison
