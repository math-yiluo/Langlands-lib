import Langlands.AbelianScheme.FieldFiniteEndomorphismSurjectiveStatement
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.FiniteIrreducibleEndomorphismSurjectiveProof
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Surjectivity of finite abelian endomorphisms over fields -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every finite endomorphism of a smooth proper geometrically connected
commutative group scheme over any field is surjective on scheme points. -/
theorem fieldFiniteEndomorphismSurjective :
    FieldFiniteEndomorphismSurjectiveStatement.{u} := by
  intro K _ G _ f h_smooth h_proper h_connected h_finite_f
  let : Smooth G.X.hom := h_smooth
  let : IsProper G.X.hom := h_proper
  let : GeometricallyConnected G.X.hom := h_connected
  let : GeometricallyIntegral G.X.hom :=
    Langlands.AbelianScheme.smoothGeometricIntegrality
      K G.X.left G.X.hom h_smooth h_connected
  let : IsIntegral G.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  let : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : CompactSpace G.X.left :=
    QuasiCompact.compactSpace_of_compactSpace G.X.hom
  let : IsNoetherian G.X.left := {}
  exact Langlands.AlgebraicGeometry.finiteIrreducibleEndomorphismSurjective
    G.X.left f.hom.hom.left h_finite_f

end Langlands.GroupScheme
