import Mathlib.RepresentationTheory.Intertwining

/-!
# Scalar twists of representations

A character in this algebraic interface is a homomorphism into the units of
the coefficient ring. No continuity or unitarity is imposed.
-/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Twist the action by a unit-valued character, on the same underlying module. -/
def twist (chi : G →* Rˣ) (rho : Representation R G V) : Representation R G V where
  toFun g := (chi g : R) • rho g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp [Module.End.mul_apply, smul_smul, mul_comm]

/-- The one-dimensional scalar representation attached to a character. -/
def characterRepresentation (chi : G →* Rˣ) : Representation R G R :=
  twist chi (Representation.trivial R G R)

/-- Twisting an intertwiner leaves its underlying linear map unchanged. -/
def twistIntertwining (chi : G →* Rˣ)
    {rho : Representation R G V} {sigma : Representation R G W}
    (f : rho.IntertwiningMap sigma) :
    (twist chi rho).IntertwiningMap (twist chi sigma) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext v
    change f.toLinearMap ((chi g : R) • rho g v) =
      (chi g : R) • sigma g (f.toLinearMap v)
    rw [map_smul]
    exact congrArg (fun w : W => (chi g : R) • w)
      (Representation.IntertwiningMap.isIntertwining rho sigma f g v)

/-- Cancel a common character twist on an intertwiner. -/
def untwistIntertwining (chi : G →* Rˣ)
    {rho : Representation R G V} {sigma : Representation R G W}
    (f : (twist chi rho).IntertwiningMap (twist chi sigma)) :
    rho.IntertwiningMap sigma where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext v
    have h := Representation.IntertwiningMap.isIntertwining
      (twist chi rho) (twist chi sigma) f g v
    change f.toLinearMap ((chi g : R) • rho g v) =
      (chi g : R) • sigma g (f.toLinearMap v) at h
    rw [map_smul] at h
    have hc := congrArg (fun w : W => (((chi g)⁻¹ : Rˣ) : R) • w) h
    simpa [smul_smul] using hc

/-- Common twisting gives a linear equivalence of spaces of intertwiners. -/
def twistIntertwiningEquiv (chi : G →* Rˣ)
    (rho : Representation R G V) (sigma : Representation R G W) :
    rho.IntertwiningMap sigma ≃ₗ[R]
      (twist chi rho).IntertwiningMap (twist chi sigma) where
  toFun := twistIntertwining chi
  invFun := untwistIntertwining chi
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_add' f g := by ext; rfl
  map_smul' r f := by ext; rfl

/-- An equivalence of representations remains an equivalence after twisting. -/
def twistEquiv (chi : G →* Rˣ)
    {rho : Representation R G V} {sigma : Representation R G W}
    (e : rho.Equiv sigma) : (twist chi rho).Equiv (twist chi sigma) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' := (twistIntertwining chi e.toIntertwiningMap).isIntertwining'

end Langlands
