import Langlands.GroupScheme.Torus.RelativeTorusImageFactorizationStatement
import Langlands.GroupScheme.Torus.RelativeTorusImage

/-! # Proof of the relative torus image factorization -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

theorem relativeTorusImageFactorization : RelativeTorusImageFactorizationStatement.{u} := by
  intro S T G f hT hG hfp
  have : IsAffineHom G.X.hom := hG
  have : LocallyOfFinitePresentation G.X.hom := hfp
  exact RelativeTorusImage.exists_factorization hT f

end Langlands.GroupScheme
