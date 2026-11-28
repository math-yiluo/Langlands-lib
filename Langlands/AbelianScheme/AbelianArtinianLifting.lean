import Langlands.AbelianScheme.AbelianArtinianLiftingReduction
import Langlands.AbelianScheme.AbelianSmoothArtinianLifting
import Langlands.AbelianScheme.PointedAbelianArtinianLifting

/-! # Abelian-scheme lifts across elementary local Artinian extensions -/

universe u

namespace Langlands.AbelianScheme

/-- An abelian scheme over the thinner ring of an elementary extension of characteristic-zero
local Artinian rings lifts to an abelian scheme over the thicker ring, with an isomorphism on
its reduction. -/
theorem abelianArtinianLifting : AbelianArtinianLiftingStatement.{u} :=
  abelianArtinianLifting_of_smoothLifting abelianSmoothArtinianLifting
    pointedAbelianArtinianLifting

end Langlands.AbelianScheme
