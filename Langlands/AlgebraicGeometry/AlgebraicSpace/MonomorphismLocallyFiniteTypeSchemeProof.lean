import Langlands.AlgebraicGeometry.AlgebraicSpace.MonomorphismLocallyFiniteTypeSchemeStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineEtaleImageAssembly
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleLocalImageDescent

/-! # Schemehood for locally finite type monomorphisms into schemes -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space admitting a locally finite type monomorphism to a
scheme is represented by a scheme over the original base. -/
theorem monomorphismLocallyFiniteTypeScheme :
    MonomorphismLocallyFiniteTypeSchemeStatement.{u} :=
  monomorphismLocallyFiniteTypeScheme_of_affine_etale_compact_images
    (by
      intro S B T V _ _ _ e _ F G π p f _ sq a haOpen w _ ha
      let M := EtaleLocalImageDescent.affineEtaleImageModel e sq a haOpen w ha
      exact ⟨M.1.val, M.1.property, ⟨M.2⟩⟩)

end Langlands.AlgebraicGeometry.AlgebraicSpace
