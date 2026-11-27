import Langlands.GroupScheme.MatrixRepresentationConjugate
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights

/-! # A closed matrix embedding adapted to the compact subgroup -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

/-- A basis change in the supplied closed matrix embedding puts the
prescribed compact subgroup inside the norm-at-most-one subgroup. -/
def RationalCompactHeightAdaptationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ K : Subgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) →
      ∃ g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)),
        IsClosedSubgroup (ρ.conjugate g) ∧
          K ≤ rationalHeightSubgroup (F := F) (ρ.conjugate g)

end Langlands.HarishChandraSchwartz
