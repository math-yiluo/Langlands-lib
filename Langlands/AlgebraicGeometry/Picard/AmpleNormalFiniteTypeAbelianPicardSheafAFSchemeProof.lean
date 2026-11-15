import Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement
import Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeIntegralFibreReduction
import Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeProof

/-! # The Picard scheme of a projective abelian scheme over a normal finite-type `ℤ`-domain
(proof)

Proof of `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement`, by the published reduction
to the noetherian integral-fibre case and the published proof of that case. -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- For every integrally closed domain `R` of finite type over `ℤ` and every abelian scheme over
`Spec R` whose total space has an ample line bundle, the fppf Picard class sheaf is represented
by a scheme over `Spec R` in which every finite set of points lies in an affine open. -/
theorem ampleNormalFiniteTypeAbelianPicardSheafAFScheme :
    AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u} :=
  ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre
    noetherianIntegralFibrePicardSheafAFScheme

end Langlands.AlgebraicGeometry.Picard
