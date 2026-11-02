import Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement
import Langlands.AbelianScheme.RelativeHomNeronExtension
import Langlands.AbelianScheme.RelativeEndomorphismAffineHomSchemePieces

/-! # Projective representability of the relative endomorphism functor -/

namespace Langlands.AbelianScheme

universe u

/-- **Projective representability of the relative endomorphism functor.** For an H-projective
abelian scheme over a noetherian affine base, the relative endomorphism functor is represented
by a coproduct of H-projective schemes over the base. -/
theorem relativeEndomorphismRepresentability : RelativeEndomorphismRepresentabilityStatement.{u} :=
  relativeEndomorphismRepresentability_of_affineHomSchemePiecesStatement
    AffineHomSchemePieces.affineHomSchemePieces

end Langlands.AbelianScheme
