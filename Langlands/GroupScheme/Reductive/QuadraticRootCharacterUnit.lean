import Langlands.GroupScheme.Torus.ExponentCocharacters
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Root-character units from quadratic units -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.QuadraticRootCharacterUnit

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]

/-- The torus point obtained by applying an integral cocharacter to a unit
on the test scheme. -/
def torusPoint (nu : I → ℤ) (T : Over (Spec (CommRingCat.of R)))
    (tau : Γ(T.left, ⊤)ˣ) :
    T ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X :=
  (Gm.pointsEquiv _ T).symm tau ≫
    (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I nu)).hom.hom

/-- Character evaluation on this actual torus point is the integral power
given by the coordinate pairing. -/
theorem charValue_torusPoint (a nu : I → ℤ)
    (T : Over (Spec (CommRingCat.of R))) (tau : Γ(T.left, ⊤)ˣ) :
    VectorGroup.charValue
        (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I a) T
        (torusPoint nu T tau) =
      ((tau ^ (∑ j, a j * nu j) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) := by
  unfold VectorGroup.charValue torusPoint
  rw [← comp_groupHom_comp,
    splitTorus.exponentCocharacter_comp_exponentCharacter,
    Gm.powerHom_apply, Gm.comp_zsmul_id, map_zpow, MulEquiv.apply_symm_apply]

/-- If the pairing is two and the unit satisfies the quadratic-cover
equation, the root-character value minus one is that same unit. -/
theorem charValue_sub_one (a nu : I → ℤ) (hpair : ∑ j, a j * nu j = 2)
    (T : Over (Spec (CommRingCat.of R))) (tau : Γ(T.left, ⊤)ˣ)
    (htau : (tau : Γ(T.left, ⊤)) ^ 2 - 1 = tau) :
    VectorGroup.charValue
        (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I a) T
        (torusPoint nu T tau) - 1 = tau := by
  rw [charValue_torusPoint, hpair]
  simpa only [zpow_ofNat, Units.val_pow_eq_pow_val] using htau

/-- The required root-character difference is invertible on every test
scheme, including tests over the zero ring. -/
theorem isUnit_charValue_sub_one (a nu : I → ℤ) (hpair : ∑ j, a j * nu j = 2)
    (T : Over (Spec (CommRingCat.of R))) (tau : Γ(T.left, ⊤)ˣ)
    (htau : (tau : Γ(T.left, ⊤)) ^ 2 - 1 = tau) :
    IsUnit (VectorGroup.charValue
      (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I a) T
      (torusPoint nu T tau) - 1) := by
  rw [charValue_sub_one a nu hpair T tau htau]
  exact tau.isUnit

end Langlands.GroupScheme.QuadraticRootCharacterUnit
