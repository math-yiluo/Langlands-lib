import Langlands.AbelianScheme.TorsionBaseChange
import Langlands.AbelianScheme.Tate.TestScheme

/-! # Base change of actual integral Tate modules -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u
namespace Langlands.GroupScheme.Tate

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S')

/-- Pullback adjunction on the actual torsion points, in additive notation. -/
def levelBaseChange (n : ℕ) :
    Level ((Over.pullback b).mapGrp.obj G) T n ≃+
      Level G ((Over.map b).obj T) n :=
  (baseChangeTorsionPointsEquiv b G (n : ℤ) T).toAdditive

@[simp] theorem toSection_levelBaseChange (n : ℕ)
    (x : Level ((Over.pullback b).mapGrp.obj G) T n) :
    Additive.toMul (toSection G ((Over.map b).obj T) n (levelBaseChange b G T n x)) =
      baseChangePointsEquiv b G T (Additive.toMul (toSection _ T n x)) := rfl

/-- The actual pullback point map commutes with quotient-power transitions. -/
theorem levelBaseChange_transition {n m : ℕ} (h : n ∣ m)
    (x : Level ((Over.pullback b).mapGrp.obj G) T m) :
    levelBaseChange b G T n (transition _ T h x) =
      transition G ((Over.map b).obj T) h (levelBaseChange b G T m x) := by
  apply toSection_injective G ((Over.map b).obj T) n
  exact _root_.map_pow (baseChangePointsEquiv b G T) (Additive.toMul x).val (m / n)

/-- The inverse pullback point map also commutes with transitions. -/
theorem levelBaseChange_symm_transition {n m : ℕ} (h : n ∣ m)
    (x : Level G ((Over.map b).obj T) m) :
    (levelBaseChange b G T n).symm (transition G ((Over.map b).obj T) h x) =
      transition _ T h ((levelBaseChange b G T m).symm x) := by
  apply (levelBaseChange b G T n).injective
  rw [AddEquiv.apply_symm_apply, levelBaseChange_transition, AddEquiv.apply_symm_apply]

/-- Coordinatewise base change on any selected actual torsion limit. -/
def integralBaseChange (P : ℕ → Prop) :
    Integral ((Over.pullback b).mapGrp.obj G) T P ≃+
      Integral G ((Over.map b).obj T) P where
  toFun x := ⟨fun n => levelBaseChange b G T n.val (x.val n), by
    intro n m h
    rw [← levelBaseChange_transition, x.property n m h]⟩
  invFun x := ⟨fun n => (levelBaseChange b G T n.val).symm (x.val n), by
    intro n m h
    rw [← levelBaseChange_symm_transition, x.property n m h]⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (levelBaseChange b G T n.val).symm_apply_apply (x.val n)
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (levelBaseChange b G T n.val).apply_symm_apply (x.val n)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (levelBaseChange b G T n.val).map_add (x.val n) (y.val n)

@[simp] theorem evaluation_integralBaseChange (P : ℕ → Prop) (n : Index P)
    (x : Integral ((Over.pullback b).mapGrp.obj G) T P) :
    evaluation G ((Over.map b).obj T) P n (integralBaseChange b G T P x) =
      levelBaseChange b G T n.val (evaluation _ T P n x) := rfl

@[simp] theorem evaluation_integralBaseChange_symm (P : ℕ → Prop) (n : Index P)
    (x : Integral G ((Over.map b).obj T) P) :
    evaluation ((Over.pullback b).mapGrp.obj G) T P n
      ((integralBaseChange b G T P).symm x) =
      (levelBaseChange b G T n.val).symm
        (evaluation G ((Over.map b).obj T) P n x) := rfl

theorem continuous_integralBaseChange (P : ℕ → Prop) :
    Continuous (integralBaseChange b G T P) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := levelBaseChange b G T n.val)).comp
    (continuous_evaluation _ T P n)

theorem continuous_integralBaseChange_symm (P : ℕ → Prop) :
    Continuous (integralBaseChange b G T P).symm := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := (levelBaseChange b G T n.val).symm)).comp
    (continuous_evaluation G ((Over.map b).obj T) P n)

/-- The full residue action is preserved coordinatewise. -/
theorem integralBaseChange_smul (P : ℕ → Prop) (a : Global.ProfiniteIntegerRing)
    (x : Integral ((Over.pullback b).mapGrp.obj G) T P) :
    integralBaseChange b G T P (a • x) = a • integralBaseChange b G T P x := by
  apply Subtype.ext
  funext n
  exact ZMod.map_smul (levelBaseChange b G T n.val).toAddMonoidHom
    (fullReduction P n a) (x.val n)

/-- Base change as a continuous linear equivalence over the full residue ring. -/
def integralBaseChangeLinearEquiv (P : ℕ → Prop) :
    Integral ((Over.pullback b).mapGrp.obj G) T P ≃L[Global.ProfiniteIntegerRing]
      Integral G ((Over.map b).obj T) P where
  __ := integralBaseChange b G T P
  map_smul' := integralBaseChange_smul b G T P
  continuous_toFun := continuous_integralBaseChange b G T P
  continuous_invFun := continuous_integralBaseChange_symm b G T P

/-- The away residue action is preserved as well. -/
theorem integralBaseChange_away_smul (m : ℕ) (a : Global.PrimeToProfiniteIntegerRing m)
    (x : Away ((Over.pullback b).mapGrp.obj G) T m) :
    integralBaseChange b G T (fun n => Nat.Coprime n m) (a • x) =
      a • integralBaseChange b G T (fun n => Nat.Coprime n m) x := by
  apply Subtype.ext
  funext n
  exact ZMod.map_smul (levelBaseChange b G T n.val).toAddMonoidHom
    (awayReduction m n a) (x.val n)

/-- Away base change over the actual prime-to-modulus residue ring. -/
def awayBaseChangeLinearEquiv (m : ℕ) :
    Away ((Over.pullback b).mapGrp.obj G) T m ≃L[Global.PrimeToProfiniteIntegerRing m]
      Away G ((Over.map b).obj T) m where
  __ := integralBaseChange b G T (fun n => Nat.Coprime n m)
  map_smul' := integralBaseChange_away_smul b G T m
  continuous_toFun := continuous_integralBaseChange b G T _
  continuous_invFun := continuous_integralBaseChange_symm b G T _

/-- Restricting the orders commutes with actual base change. -/
theorem integralBaseChange_restrictAway (m : ℕ)
    (x : Full ((Over.pullback b).mapGrp.obj G) T) :
    integralBaseChange b G T (fun n => Nat.Coprime n m) (restrictAway _ T m x) =
      restrictAway G ((Over.map b).obj T) m
        (integralBaseChange b G T (fun _ => True) x) := rfl

variable {T}

/-- Naturality of finite base change in the test scheme. -/
theorem levelBaseChange_testRestrict {T' : Over S'} (a : T' ⟶ T) (n : ℕ)
    (x : Level ((Over.pullback b).mapGrp.obj G) T n) :
    levelBaseChange b G T' n (levelRestrict _ a n x) =
      levelRestrict G ((Over.map b).map a) n (levelBaseChange b G T n x) := by
  apply toSection_injective G ((Over.map b).obj T') n
  exact baseChangePointsEquiv_naturality b G a (Additive.toMul x).val

/-- Naturality of the integral comparison in the test scheme. -/
theorem integralBaseChange_testRestrict {T' : Over S'} (P : ℕ → Prop) (a : T' ⟶ T)
    (x : Integral ((Over.pullback b).mapGrp.obj G) T P) :
    integralBaseChange b G T' P (testRestrict _ P a x) =
      testRestrict G P ((Over.map b).map a) (integralBaseChange b G T P x) := by
  apply Subtype.ext
  funext n
  exact levelBaseChange_testRestrict b G a n.val (x.val n)

variable (T) {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- Naturality of finite base change in the actual group-scheme homomorphism. -/
theorem levelBaseChange_map (f : G ⟶ H) (n : ℕ)
    (x : Level ((Over.pullback b).mapGrp.obj G) T n) :
    levelBaseChange b H T n (levelMap T ((Over.pullback b).mapGrp.map f) n x) =
      levelMap ((Over.map b).obj T) f n (levelBaseChange b G T n x) := by
  apply toSection_injective H ((Over.map b).obj T) n
  exact baseChangePointsEquiv_comp b f T (Additive.toMul x).val

/-- Naturality of the integral comparison in the group scheme. -/
theorem integralBaseChange_map (P : ℕ → Prop) (f : G ⟶ H)
    (x : Integral ((Over.pullback b).mapGrp.obj G) T P) :
    integralBaseChange b H T P (map T P ((Over.pullback b).mapGrp.map f) x) =
      map ((Over.map b).obj T) P f (integralBaseChange b G T P x) := by
  apply Subtype.ext
  funext n
  exact levelBaseChange_map b T f n.val (x.val n)

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S) (T : Over S')

/-- Actual integral Tate base change for a bundled abelian scheme. -/
abbrev integralBaseChange (P : ℕ → Prop) :
    Integral ((AbelianScheme.baseChange b).obj A) T P ≃L[Global.ProfiniteIntegerRing]
      Integral A ((Over.map b).obj T) P :=
  GroupScheme.Tate.integralBaseChangeLinearEquiv b A.toGrp T P

/-- Actual away Tate base change for a bundled abelian scheme. -/
abbrev awayBaseChange (m : ℕ) :
    Away ((AbelianScheme.baseChange b).obj A) T m ≃L[Global.PrimeToProfiniteIntegerRing m]
      Away A ((Over.map b).obj T) m :=
  GroupScheme.Tate.awayBaseChangeLinearEquiv b A.toGrp T m

/-- Pointed base change at a field-valued point over the new base. -/
abbrev fullBaseChangeAt {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ S') :
    FullAt ((AbelianScheme.baseChange b).obj A) t ≃L[Global.ProfiniteIntegerRing]
      FullAt A (t ≫ b) :=
  integralBaseChange b A (Over.mk t) (fun _ => True)

/-- Pointed away base change uses the same prime-to-modulus scalar ring. -/
abbrev awayBaseChangeAt {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ S') (m : ℕ) :
    AwayAt ((AbelianScheme.baseChange b).obj A) t m ≃L[Global.PrimeToProfiniteIntegerRing m]
      AwayAt A (t ≫ b) m :=
  awayBaseChange b A (Over.mk t) m

variable {A} {B : AbelianScheme S}

/-- Actual abelian-scheme homomorphisms commute with the base-change comparison. -/
theorem integralBaseChange_map (P : ℕ → Prop) (f : A ⟶ B)
    (x : Integral ((AbelianScheme.baseChange b).obj A) T P) :
    integralBaseChange b B T P (map T P ((AbelianScheme.baseChange b).map f) x) =
      map ((Over.map b).obj T) P f (integralBaseChange b A T P x) :=
  GroupScheme.Tate.integralBaseChange_map b T P (AbelianScheme.groupHom f) x

end Langlands.AbelianScheme.Tate
