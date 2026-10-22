import Mathlib.RepresentationTheory.Basic

/-! # Matrix coefficients as a bilinear map -/

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- The matrix coefficient is `g ↦ ℓ (ρ g v)`, linear in each of `ℓ` and `v`.
The functional belongs to the full algebraic dual; smoothness is separate. -/
def matrixCoefficient (ρ : Representation R G V) :
    Module.Dual R V →ₗ[R] V →ₗ[R] (G → R) where
  toFun ℓ :=
    { toFun := fun v g => ℓ (ρ g v)
      map_add' v w := by
        ext g
        simp
      map_smul' a v := by
        ext g
        simp }
  map_add' ℓ m := by
    ext v g
    rfl
  map_smul' a ℓ := by
    ext v g
    rfl

end Langlands
