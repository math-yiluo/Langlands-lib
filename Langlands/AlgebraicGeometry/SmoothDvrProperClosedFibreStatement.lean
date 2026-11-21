import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Properness from the closed fibre over a discrete valuation ring -/

universe u

open AlgebraicGeometry CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry

/-- A smooth separated finite-type scheme with geometrically connected
fibres over a discrete valuation ring is proper if its closed fibre is proper. -/
def SmoothDvrProperClosedFibreStatement : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of V)),
    Smooth p → IsSeparated p → QuasiCompact p → GeometricallyConnected p →
    IsProper (pullback.snd p (Spec.algebraMap V (IsLocalRing.ResidueField V))) → IsProper p

end Langlands.AlgebraicGeometry
