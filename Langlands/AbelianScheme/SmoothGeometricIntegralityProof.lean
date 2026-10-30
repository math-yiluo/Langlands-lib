import Langlands.AbelianScheme.SmoothGeometricIntegralityStatement
import Langlands.AlgebraicGeometry.SmoothDomainStalksProof
import Langlands.AlgebraicGeometry.ConnectedLocallyNoetherianDomainStalksIntegralProof

/-! # Geometric integrality of smooth geometrically connected schemes over fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A smooth geometrically connected scheme over any field is geometrically integral. -/
theorem smoothGeometricIntegrality : SmoothGeometricIntegrality.{u} := by
  intro K _ X p hp hc
  let : Smooth p := hp
  let : GeometricallyConnected p := hc
  refine ⟨?_⟩
  intro L _ y Z fst snd h
  let : Smooth snd := MorphismProperty.of_isPullback h hp
  have hnoeth : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian snd
  have hconn : ConnectedSpace Z :=
    GeometricallyConnected.geometrically_connectedSpace y fst snd h
  exact Langlands.AlgebraicGeometry.connectedLocallyNoetherianDomainStalksIntegral
    Z hnoeth hconn (Langlands.AlgebraicGeometry.smoothDomainStalks L Z snd inferInstance)

end Langlands.AbelianScheme
