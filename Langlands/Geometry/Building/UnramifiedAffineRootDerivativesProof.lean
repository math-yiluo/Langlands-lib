import Langlands.Geometry.Building.UnramifiedAffineRootDerivativesStatement
import Langlands.Geometry.Building.MaximalUnramifiedBuildingExistence
import Langlands.Geometry.Building.QuasiSplitDerivativeAffineRootsProof

/-! # Derivatives of affine roots over the maximal unramified field -/

noncomputable section

universe u

open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The affine roots of every supplied building datum over the maximal unramified
field have the full relative root system as their derivatives. -/
theorem unramifiedAffineRootDerivatives :
    UnramifiedAffineRootDerivativesStatement.{u} := by
  intro F _ _ _ _ H _ C
  exact quasiSplitDerivativeAffineRoots (inertiaFixedField F) (MaximalUnramified.valuation F)
    (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F) H
    (MaximalUnramified.isQuasiSplit F C.isConnectedReductive) C.S C.i C.isMaximalSplitTorus
    C.apartment C.centralizer C.isOmegaCompatible

end Langlands.Geometry.Building
