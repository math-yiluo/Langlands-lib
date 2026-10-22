import Mathlib.RepresentationTheory.Intertwining

/-! # Algebraic dual maps of representations

These constructions use Mathlib's existing full algebraic dual action.
No smoothness or topology is imposed.
-/

noncomputable section

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Pullback of functionals along an intertwiner, with the algebraic dual actions. -/
def dualIntertwining (f : ρ.IntertwiningMap σ) : σ.dual.IntertwiningMap ρ.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' g := by
    ext ℓ v
    change ℓ (σ g⁻¹ (f v)) = ℓ (f (ρ g⁻¹ v))
    rw [f.isIntertwining]

/-- An equivalence of representations induces the reverse equivalence of full duals. -/
def dualEquiv (e : ρ.Equiv σ) : σ.dual.Equiv ρ.dual where
  toLinearEquiv := e.toLinearEquiv.dualMap
  isIntertwining' := (dualIntertwining e.toIntertwiningMap).isIntertwining'

/-- Evaluation as an intertwiner into the full algebraic bidual.
No injectivity or surjectivity is asserted over an arbitrary coefficient ring. -/
def bidualIntertwining (ρ : Representation R G V) : ρ.IntertwiningMap ρ.dual.dual where
  toLinearMap := Module.Dual.eval R V
  isIntertwining' g := by
    ext v ℓ
    change ℓ (ρ g v) = ℓ (ρ (g⁻¹)⁻¹ v)
    rw [inv_inv]

end Langlands
