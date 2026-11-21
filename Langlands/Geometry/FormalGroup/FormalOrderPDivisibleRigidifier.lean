import Langlands.Geometry.FormalGroup.FormalModuleRationalTower
import Langlands.Geometry.FormalGroup.PDivisibleOrderRigidifier
import Langlands.Geometry.FormalGroup.OrderRationalMorphism

/-! # The split rigidifier induced by a formal order-linear quasi-isogeny -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

open CategoryTheory GroupScheme.Cartier

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Algebra ℤ_[p] R]
variable {A : Type v} [Ring A] [Algebra ℤ_[p] A]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw ℤ_[p] R σ} {N : ModuleLaw ℤ_[p] R τ}
variable {E : OrderAction A M} {E' : OrderAction A N}

namespace QuasiIsogeny

/-- An order-linear formal quasi-isogeny restricts to an actual order-linear
rational map of the finite-level towers. -/
def pDivisibleMap (f : QuasiIsogeny ℚ_[p] E E')
    (hM : M.IsPiDivisible (p : ℤ_[p])) (hN : N.IsPiDivisible (p : ℤ_[p])) :
    PDivisibleGroup.OrderQuasiIsogeny (E.pDivisibleAction hM) (E'.pDivisibleAction hN) where
  val := f.toModuleQuasiIsogeny.pDivisibleMap hM hN
  commutes a := by
    let t := ModuleLaw.RationalHom.pDivisibleMap hM hN
    have h₁ := ModuleLaw.RationalHom.pDivisibleMap_comp hM hM hN f.hom.val
      (ModuleLaw.RationalHom.ofHom (E.action a))
    have h₂ := ModuleLaw.RationalHom.pDivisibleMap_comp hM hN hN
      (ModuleLaw.RationalHom.ofHom (E'.action a)) f.hom.val
    rw [ModuleLaw.RationalHom.pDivisibleMap_ofHom] at h₁ h₂
    exact h₁.symm.trans ((congrArg t (f.hom.commutes a)).trans h₂)

/-- The actual split polarized rigidifier induced by a formal primal map and
one multiplier. The dual tower uses finite Cartier exactness. -/
def splitPDivisibleRigidifier (f : QuasiIsogeny ℚ_[p] E E')
    (hM : M.IsPiDivisible (p : ℤ_[p])) (hN : N.IsPiDivisible (p : ℤ_[p]))
    (hExact : FiniteCartierDualExactnessStatement.{u}) (c : ℚ_[p]ˣ) :
    PDivisibleGroup.OrderQuasiIsogeny
      (PDivisibleGroup.splitOrderAction (E.pDivisibleAction hM) hExact)
      (PDivisibleGroup.splitOrderAction (E'.pDivisibleAction hN) hExact) :=
  PDivisibleGroup.splitOrderRigidifier hExact (f.pDivisibleMap hM hN) c

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.OrderAction
