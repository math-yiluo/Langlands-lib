import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # Raynaud's affineness criterion for group schemes over a DVR -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A flat finite-type group scheme over a discrete valuation ring with affine
generic fibre is affine if and only if it is separated. This is Raynaud's
criterion as stated in Prasad--Yu, Proposition 3.1. -/
def DvrGenericAffinenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    Flat G.X.hom → LocallyOfFiniteType G.X.hom → QuasiCompact G.X.hom →
    IsAffineHom
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).X.hom →
    (IsAffineHom G.X.hom ↔ IsSeparated G.X.hom)

end Langlands.GroupScheme
