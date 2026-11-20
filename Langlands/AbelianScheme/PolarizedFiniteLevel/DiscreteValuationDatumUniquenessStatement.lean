import Langlands.AbelianScheme.PolarizedFiniteLevel.Pullback
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Uniqueness of ordinary polarized full-level data over a discrete valuation ring -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Two ordinary polarized full-level data over the spectrum of a discrete valuation ring `R`
in which the level `n` is a unit are isomorphic if their pullbacks to the spectrum of the
fraction field `K` are isomorphic. This proposition is a statement, not a proof of it. -/
def DiscreteValuationDatumUniquenessStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (g d n : ℕ) (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K],
    IsUnit (n : R) →
    ∀ a b : Datum P (Spec (CommRingCat.of R)) g d n,
      Isomorphic (a.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K))))
          (b.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))) →
        Isomorphic a b

end Langlands.AbelianScheme.PolarizedFiniteLevel
