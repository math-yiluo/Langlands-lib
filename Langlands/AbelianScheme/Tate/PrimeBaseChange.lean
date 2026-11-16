import Langlands.AbelianScheme.Tate.IntegralBaseChange
import Langlands.AbelianScheme.Tate.RationalPrimeHom
import Langlands.AbelianScheme.RationalBaseChange
import Mathlib.LinearAlgebra.Trace

/-! # Base change of the actual prime Tate action and trace -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.GroupScheme.Tate.PrimeAdic

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S')
  (p : ℕ) [Fact p.Prime]

/-- Pullback comparison on the actual coherent prime-power torsion sequences. -/
def integralBaseChange :
    Integral ((Over.pullback b).mapGrp.obj G) T p ≃ₗ[ℤ_[p]]
      Integral G ((Over.map b).obj T) p where
  toFun x := ⟨fun n => Tate.levelBaseChange b G T (p ^ n) (x.val n), by
    intro n
    rw [← Tate.levelBaseChange_transition, x.property n]⟩
  invFun x := ⟨fun n => (Tate.levelBaseChange b G T (p ^ n)).symm (x.val n), by
    intro n
    rw [← Tate.levelBaseChange_symm_transition, x.property n]⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (Tate.levelBaseChange b G T (p ^ n)).symm_apply_apply (x.val n)
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (Tate.levelBaseChange b G T (p ^ n)).apply_symm_apply (x.val n)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (Tate.levelBaseChange b G T (p ^ n)).map_add (x.val n) (y.val n)
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact ZMod.map_smul (Tate.levelBaseChange b G T (p ^ n)).toAddMonoidHom
      (PadicInt.toZModPow n a) (x.val n)

/-- Scalar extension gives the actual rational prime Tate pullback comparison. -/
def rationalBaseChange :
    Rational ((Over.pullback b).mapGrp.obj G) T p ≃ₗ[ℚ_[p]]
      Rational G ((Over.map b).obj T) p :=
  (integralBaseChange b G T p).baseChange ℤ_[p] ℚ_[p] _ _

@[simp]
theorem rationalBaseChange_tmul (q : ℚ_[p])
    (x : Integral ((Over.pullback b).mapGrp.obj G) T p) :
    rationalBaseChange b G T p (q ⊗ₜ[ℤ_[p]] x) =
      q ⊗ₜ[ℤ_[p]] integralBaseChange b G T p x := rfl

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- The integral comparison intertwines every actual group-scheme homomorphism. -/
theorem integralBaseChange_map (f : G ⟶ H)
    (x : Integral ((Over.pullback b).mapGrp.obj G) T p) :
    integralBaseChange b H T p (map T p ((Over.pullback b).mapGrp.map f) x) =
      map ((Over.map b).obj T) p f (integralBaseChange b G T p x) := by
  apply Subtype.ext
  funext n
  exact Tate.levelBaseChange_map b T f (p ^ n) (x.val n)

/-- The rational comparison intertwines every actual group-scheme homomorphism. -/
theorem rationalBaseChange_map (f : G ⟶ H)
    (x : Rational ((Over.pullback b).mapGrp.obj G) T p) :
    rationalBaseChange b H T p (rationalMap T p ((Over.pullback b).mapGrp.map f) x) =
      rationalMap ((Over.map b).obj T) p f (rationalBaseChange b G T p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
      simp only [rationalMap_tmul, rationalBaseChange_tmul, integralBaseChange_map]
  | add x y hx hy => simp only [map_add, hx, hy]

end Langlands.GroupScheme.Tate.PrimeAdic

namespace Langlands.AbelianScheme.Tate.PrimeAdic

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (A : AbelianScheme S) (T : Over S') (p : ℕ) [Fact p.Prime]

/-- Actual integral prime Tate base change for bundled abelian schemes. -/
abbrev integralBaseChange :
    Integral ((AbelianScheme.baseChange b).obj A) T p ≃ₗ[ℤ_[p]]
      Integral A ((Over.map b).obj T) p :=
  GroupScheme.Tate.PrimeAdic.integralBaseChange b A.toGrp T p

/-- Actual rational prime Tate base change for bundled abelian schemes. -/
abbrev rationalBaseChange :
    Rational ((AbelianScheme.baseChange b).obj A) T p ≃ₗ[ℚ_[p]]
      Rational A ((Over.map b).obj T) p :=
  GroupScheme.Tate.PrimeAdic.rationalBaseChange b A.toGrp T p

variable {A} {B : AbelianScheme S}

/-- Base change is natural for actual integral abelian-scheme homomorphisms. -/
theorem rationalBaseChange_map (f : A ⟶ B)
    (x : Rational ((AbelianScheme.baseChange b).obj A) T p) :
    rationalBaseChange b B T p (rationalMap T p ((AbelianScheme.baseChange b).map f) x) =
      rationalMap ((Over.map b).obj T) p f (rationalBaseChange b A T p x) :=
  GroupScheme.Tate.PrimeAdic.rationalBaseChange_map b T p (AbelianScheme.groupHom f) x

/-- Base change is natural for the actual rationalized homomorphism action. -/
theorem rationalBaseChange_homMap (f : Hom0 A B)
    (x : Rational ((AbelianScheme.baseChange b).obj A) T p) :
    rationalBaseChange b B T p (rationalHomMap T p (rationalBaseChangeHom b f) x) =
      rationalHomMap ((Over.map b).obj T) p f (rationalBaseChange b A T p x) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
      simp only [rationalBaseChangeHom_tmul, rationalHomMap_tmul, LinearMap.smul_apply]
      rw [map_rat_smul, rationalBaseChange_map]
  | add f g hf hg =>
      simp only [_root_.map_add, LinearMap.add_apply, hf, hg]

variable (A)

/-- The actual rational prime Tate trace is unchanged under pullback when the
test object is mapped to the original base. -/
theorem trace_rationalHomMap_baseChange (f : End0 A) :
    LinearMap.trace ℚ_[p] (Rational ((AbelianScheme.baseChange b).obj A) T p)
        (rationalHomMap T p (rationalBaseChangeHom b f)) =
      LinearMap.trace ℚ_[p] (Rational A ((Over.map b).obj T) p)
        (rationalHomMap ((Over.map b).obj T) p f) := by
  let e := rationalBaseChange b A T p
  have he : e.conj (rationalHomMap T p (rationalBaseChangeHom b f)) =
      rationalHomMap ((Over.map b).obj T) p f := by
    apply LinearMap.ext
    intro x
    change e (rationalHomMap T p (rationalBaseChangeHom b f) (e.symm x)) = _
    rw [rationalBaseChange_homMap, e.apply_symm_apply]
  exact (LinearMap.trace_conj' _ e).symm.trans
    (congrArg (LinearMap.trace ℚ_[p] _) he)

end Langlands.AbelianScheme.Tate.PrimeAdic
