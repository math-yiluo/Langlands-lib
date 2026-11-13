import Mathlib.Basic.Complex.Basic
import Langlands.Weil.Representation.Restriction
import Langlands.Weil.Representation.Dual

/-! # Restriction and the algebraic dual of a finite representation -/

noncomputable section

universe uG uH uA

namespace Langlands.FiniteRepresentation

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- Restriction commutes with duals; the underlying map is the identity. -/
def restrictDualEquiv (φ : H →* G) (A : FiniteRepresentation.{0, uG, uA} ℂ G) :
    Equiv (restrict φ (dual A)) (dual (restrict φ A)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' h := by
    apply LinearMap.ext
    intro ℓ
    change (A.representation.dual (φ h)) ℓ = Representation.dual (A.representation.comp φ) h ℓ
    rw [Representation.dual_apply, Representation.dual_apply, MonoidHom.comp_apply, map_inv φ h]

end Langlands.FiniteRepresentation
