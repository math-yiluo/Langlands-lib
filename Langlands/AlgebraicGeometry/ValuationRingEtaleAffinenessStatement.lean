import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Valuation.ValuationRing

/-! # Affineness of separated quasi-compact etale schemes over valuation rings -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A quasi-compact separated etale morphism to the spectrum of an arbitrary
valuation domain is affine. No rank or noetherian hypothesis is imposed. -/
def ValuationRingEtaleAffinenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    QuasiCompact f → IsSeparated f → Etale f → IsAffineHom f

end Langlands.AlgebraicGeometry
