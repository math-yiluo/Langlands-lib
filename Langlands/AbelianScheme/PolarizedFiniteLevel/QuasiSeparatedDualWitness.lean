import Langlands.AbelianScheme.PolarizedFiniteLevel.Data
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse

/-! # Dual witnesses over quasi-separated bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

/-- Over a quasi-separated base every abelian scheme has a dual witness: the Library's
proved existence and geometry of the universal Picard-zero family, together with the
chosen tensor inverse of the Poincaré bundle and its evaluation. -/
def DualWitness.ofQuasiSeparated {S : Scheme.{u}} [QuasiSeparatedSpace S]
    (A : AbelianScheme S) : DualWitness A where
  hasDual := relativeDualSchemeExistence S A
  geometry := relativeDualSchemeGeometry S A _
  inverseBundle := ((RigidifiedLineBundle.forget _).obj
    (poincareFamily A (relativeDualSchemeExistence S A))).inverse
  evaluation := LineBundle.tensorInverseIso ((RigidifiedLineBundle.forget _).obj
    (poincareFamily A (relativeDualSchemeExistence S A)))

end Langlands.AbelianScheme.PolarizedFiniteLevel
