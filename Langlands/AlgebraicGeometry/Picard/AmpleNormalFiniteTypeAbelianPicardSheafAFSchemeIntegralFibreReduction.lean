import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement
import Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeStatement

/-! # The projective abelian Picard statement from the general noetherian integral-fibre case -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency.types false in
/-- The structure morphism of an abelian scheme has geometrically integral fibres. -/
theorem abelianScheme_geometricallyIntegral {S : Scheme.{u}} (A : Langlands.AbelianScheme S) :
    GeometricallyIntegral A.X.hom := by
  rw [GeometricallyIntegral.iff_geometricallyIntegral_fiber]
  intro s
  have hs : Smooth (A.X.hom.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ A.smooth
  have hc : GeometricallyConnected (A.X.hom.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ A.geometricallyConnected
  exact Langlands.AbelianScheme.smoothGeometricIntegrality _ _ _ hs hc

/-- The general Picard statement for pointed proper flat families with geometrically integral
fibres over noetherian affine bases gives the projective abelian case over normal finite-type
`ℤ`-domains. -/
theorem ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre
    (h : NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u}) :
    AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u} := by
  intro R _ _ _ _ A hL
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  refine h R A.X.left A.X.hom inferInstance inferInstance (abelianScheme_geometricallyIntegral A)
    ⟨(η[A.X]).left, ?_⟩ hL
  simp

end Langlands.AlgebraicGeometry.Picard
