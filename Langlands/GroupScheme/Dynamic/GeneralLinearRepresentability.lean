import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # Representability of `P(λ)`, `Z(λ)` and `U(λ)` for the diagonal cocharacters of `GL_n`

For weights `e : n → ℤ` and the diagonal cocharacter `λ` of `GL_{n,R}`, the dynamic subgroup
functors `P(λ)`, `Z(λ)` and `U(λ)` are represented by the block parabolic, block Levi and block
unipotent closed subgroup schemes of `GL_{n,R}`: their inclusions are closed immersions whose
points over every scheme `T` over `Spec R` are exactly the points of `P(λ)`, `Z(λ)` and `U(λ)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) (e : n → ℤ)

/-- `P(λ)` for the diagonal cocharacter is represented by the block parabolic subgroup scheme. -/
theorem isRepresentedBy_parabolic_diagonalCocharacter :
    (Dynamic.parabolic (diagonalCocharacter n R e)).IsRepresentedBy (blockParabolicHom n R e) := by
  rw [parabolic_diagonalCocharacter]
  exact isRepresentedBy_blockParabolic n R e

/-- `Z(λ)` for the diagonal cocharacter is represented by the block Levi subgroup scheme. -/
theorem isRepresentedBy_centralizer_diagonalCocharacter :
    (Dynamic.centralizer (diagonalCocharacter n R e)).IsRepresentedBy (blockLeviHom n R e) := by
  rw [centralizer_diagonalCocharacter]
  exact isRepresentedBy_blockLevi n R e

/-- `U(λ)` for the diagonal cocharacter is represented by the block unipotent subgroup
scheme. -/
theorem isRepresentedBy_unipotent_diagonalCocharacter :
    (Dynamic.unipotent (diagonalCocharacter n R e)).IsRepresentedBy (blockUnipotentHom n R e) := by
  rw [unipotent_diagonalCocharacter]
  exact isRepresentedBy_blockUnipotent n R e

/-- `P(λ)`, `Z(λ)` and `U(λ)` for the diagonal cocharacter are represented by closed subgroup
schemes of `GL_{n,R}`. -/
theorem exists_isClosedSubgroup_isRepresentedBy_diagonalCocharacter :
    (∃ (P : GroupScheme (Spec R)) (i : P ⟶ groupScheme n R),
        IsClosedSubgroup i ∧ (Dynamic.parabolic (diagonalCocharacter n R e)).IsRepresentedBy i) ∧
      (∃ (Z : GroupScheme (Spec R)) (i : Z ⟶ groupScheme n R),
        IsClosedSubgroup i ∧
          (Dynamic.centralizer (diagonalCocharacter n R e)).IsRepresentedBy i) ∧
      (∃ (U : GroupScheme (Spec R)) (i : U ⟶ groupScheme n R),
        IsClosedSubgroup i ∧ (Dynamic.unipotent (diagonalCocharacter n R e)).IsRepresentedBy i) :=
  ⟨⟨_, _, isClosedSubgroup_blockParabolicHom n R e,
      isRepresentedBy_parabolic_diagonalCocharacter n R e⟩,
    ⟨_, _, isClosedSubgroup_blockLeviHom n R e,
      isRepresentedBy_centralizer_diagonalCocharacter n R e⟩,
    ⟨_, _, isClosedSubgroup_blockUnipotentHom n R e,
      isRepresentedBy_unipotent_diagonalCocharacter n R e⟩⟩

end Langlands.GroupScheme.GeneralLinear
