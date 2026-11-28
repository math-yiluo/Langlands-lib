import Langlands.Geometry.Building.KPTorusRegressionStatement
import Langlands.Geometry.Building.TorusFiveAxiomConstruction
import Langlands.GroupScheme.Rational.AnisotropicCentralizerNormKernel
import Langlands.GroupScheme.Rational.AnisotropicCompactnessProof
import Langlands.GroupScheme.Torus.RelativeCommutativity

/-!
# Anisotropic tori: proof of `KPAnisotropicTorusStatement`
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building

/-- An anisotropic torus `T` over a nonarchimedean local field `F`: `T(F)^1 = T(F)`, `T(F)` is
compact in the canonical topology, and for every KP building datum satisfying the one-group
axioms every point of the enlarged building is fixed by all of `T(F)`. -/
theorem kpAnisotropicTorus : KPAnisotropicTorusStatement.{u} := by
  intro F _ _ _ _ T hT hA
  let : IsAffineHom T.X.hom := hT.isRelativeTorus.isAffineHom
  have hred : IsConnectedReductive T := hT.isConnectedReductive_of_fieldSplitting
  have hker : rationalCommonNormKernel T = ⊤ := hA.rationalCommonNormKernel_eq_top hred
  refine ⟨hker, (anisotropicCompactness_proof F T hred).2 hA, fun D _ z => ?_⟩
  let U := hT.isRelativeTorus.commGroupScheme
  have : IsAffineHom U.toGrp.X.hom := ‹IsAffineHom T.X.hom›
  let B := D.base.toValuationBuildingData
  exact (B.enlargedStabilizer_eq_compactStabilizer z).trans
    ((ValuationBuildingData.compactStabilizer_eq_normKernel_of_commutative (T := U) B _).trans
      hker)

end Langlands.Geometry.Building
