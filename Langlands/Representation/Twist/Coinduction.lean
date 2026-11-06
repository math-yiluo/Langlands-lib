import Langlands.Representation.Twist.Definitions
import Mathlib.RepresentationTheory.Coinduced

/-!
# Scalar character twists of actual coinduced representations

Multiplication by the inverse character on the ambient variable moves a
restricted character twist through the actual equivariant-function model.
-/

noncomputable section

universe uR uG uH uV

namespace Langlands

variable {R : Type uR} {G : Type uG} {H : Type uH} {V : Type uV}
variable [CommRing R] [Group G] [Group H] [AddCommGroup V] [Module R V]

/-- A restricted scalar twist commutes with actual coinduction. The map
multiplies the value at `g` by the inverse of the ambient character at `g`. -/
def coindTwistEquiv (φ : H →* G) (χ : G →* Rˣ) (ρ : Representation R H V) :
    (Representation.coind φ (twist (χ.comp φ) ρ)).Equiv
      (twist χ (Representation.coind φ ρ)) where
  toLinearEquiv := {
    toFun f := ⟨fun g => (((χ g)⁻¹ : Rˣ) : R) • f.val g, by
      intro h g
      dsimp only
      rw [f.property]
      simp [twist, map_mul, smul_smul, mul_comm, mul_left_comm]⟩
    invFun f := ⟨fun g => (χ g : R) • f.val g, by
      intro h g
      dsimp only
      rw [f.property]
      simp [twist, map_mul, smul_smul, mul_comm]⟩
    left_inv f := by
      apply Subtype.ext
      funext g
      simp [smul_smul]
    right_inv f := by
      apply Subtype.ext
      funext g
      simp [smul_smul]
    map_add' f f' := by
      apply Subtype.ext
      funext g
      exact smul_add _ _ _
    map_smul' r f := by
      apply Subtype.ext
      funext g
      exact smul_comm _ _ _ }
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change (((χ x)⁻¹ : Rˣ) : R) • f.val (x * g) =
      (χ g : R) • ((((χ (x * g))⁻¹ : Rˣ) : R) • f.val (x * g))
    simp [map_mul, smul_smul, mul_comm]

end Langlands
