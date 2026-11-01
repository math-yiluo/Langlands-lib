import Langlands.CommutativeAlgebra.RegularLocalAwayPicardStatement
import Langlands.CommutativeAlgebra.RegularLocalFiniteProjectiveDimensionProof
import Langlands.CommutativeAlgebra.LocalizationPicardOfFiniteProjectiveDimension

/-! # Picard vanishing after inverting an element of a regular local ring -/

universe u

namespace Langlands.CommutativeAlgebra

/-- The Picard group of a regular local ring with any one element inverted is
trivial (Stacks Project, Lemma 15.123.1, Tag 0AFZ). -/
theorem regularLocalAwayPicard : RegularLocalAwayPicardStatement.{u} := by
  intro R _ hR f
  let : IsRegularLocalRing R := hR
  exact subsingleton_pic_localization_of_finite_projectiveDimension
    (R := R) (regularLocalFiniteProjectiveDimension R hR) (Submonoid.powers f)

end Langlands.CommutativeAlgebra
