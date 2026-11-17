import Langlands.GroupScheme.Torus.DiagonalizableFppfQuotient
import Langlands.GroupScheme.DiagonalizableQuotientModelTransport

/-! # Central multiplicative-type quotients over arbitrary bases -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The direct affine diagonalizable quotient is constructed by the actual
invariant spectrum and its descended group structure. -/
theorem affineDiagonalizableModelQuotient :
    AffineDiagonalizableModelQuotientStatement.{u} := by
  intro R M _ _ G _ i hi hn
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact ⟨CharacterAction.quotientGroup i hi hn,
    CharacterAction.quotientHom i hi hn,
    CharacterAction.quotientGroup_isAffineHom i hi hn,
    CharacterAction.quotientHom_isFppfQuotient i hi hn⟩

/-- Every closed central multiplicative-type subgroup of a smooth affine group
with connected geometric fibers has an affine fppf quotient over its arbitrary
base, with its full all-test kernel. -/
theorem relativeCentralMultiplicativeTypeQuotient :
    RelativeCentralMultiplicativeTypeQuotientStatement.{u} :=
  relativeCentralMultiplicativeTypeQuotient_of_affineDiagonalizableModel
    affineDiagonalizableModelQuotient

end Langlands.GroupScheme
