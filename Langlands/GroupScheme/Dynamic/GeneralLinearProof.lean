import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit
import Langlands.GroupScheme.Dynamic.GeneralLinearStatement

/-! # Dynamic subgroups of `GL_n` for diagonal cocharacters: proof -/

universe u

namespace Langlands.GroupScheme.GeneralLinear

/-- The dynamic subgroups, the limit map and the decomposition of `P(λ)` for diagonal and
block-shape cocharacters of `GL_n` over every commutative ring. -/
theorem dynamicStatement : DynamicStatement.{u} :=
  ⟨fun n _ _ R e => ⟨parabolic_diagonalCocharacter n R e, centralizer_diagonalCocharacter n R e,
      unipotent_diagonalCocharacter n R e⟩,
    fun _ B R => ⟨parabolic_blockShapeCocharacter B R, centralizer_blockShapeCocharacter B R,
      unipotent_blockShapeCocharacter B R⟩,
    fun _ _ _ _ e _ _ _ => hasLimit_diagonalCocharacter_iff e,
    fun n _ _ R e T => leviDecomposition_diagonalCocharacter n R e T,
    fun _ _ _ _ _ _ => hasLimit_blockShapeCocharacter_iff⟩

end Langlands.GroupScheme.GeneralLinear
