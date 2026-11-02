import Langlands.AbelianScheme.PolarizedFiniteLevel.Data
import Langlands.AlgebraicGeometry.Picard.AmpleMumfordBaseChange
import Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordStatement

/-! # Ampleness of a diagonal bundle from an actual ample presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard

/-- Over a one-point base, the diagonal Poincaré bundle of the Mumford map
of an actual ample bundle is ample. -/
def AmpleMumfordDiagonalStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S : Scheme.{u}) [Unique S]
    (A : AbelianScheme S) (W : DualWitness A) (f : A.X ⟶ dualScheme A W.hasDual),
    HasAmpleMumfordPresentation P.preservation P.square A W.hasDual f →
      (poincareDiagonalBundle A W.hasDual f).IsAmple

end Langlands.AbelianScheme.PolarizedFiniteLevel
