import Langlands.Geometry.Building.KPParahoric
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Geometry.Building.KPNilpotentCoset
import Langlands.GroupScheme.IntegralModel.LieLatticeAdjoint

/-!
# Putting a contracting cocharacter in the apartment torus by parahoric conjugation

A target for the contraction conclusion used in the proof of KP Proposition 13.6.7. This
forgets both compatibility with the point (KP Definition 13.6.1) and the dominance
inequalities in KP Proposition 13.6.4. It concerns points of the connected parahoric, not the
full fixer, on supplied building data with the apartment axioms.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- For a nilpotent Lie vector `X` and a point `x` in the closure of an apartment chamber, some
`p ∈ P_x` carries `X` to a vector contracted by a cocharacter of the actual apartment torus.
Here `P_x` is the connected parahoric of the supplied data. This is the contraction clause of
KP Proposition 13.6.4 with extension of the cocharacter and the dominance inequalities omitted. -/
def ParahoricContractionInApartmentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G),
    P.SatisfiesApartmentAxioms →
    ∀ (c x : P.Apartment), (∀ ψ ∈ P.affineRoots, ψ c ≠ 0) →
      x ∈ AffineRootSystem.facetClosure P.affineRoots c →
      ∀ X : GenericLie 𝒪[F] G, IsCocharacterNilpotent X →
        ∃ p ∈ P.parahoricAt x, ∃ ν : cocharacterLattice P.S,
          GenericLie.equiv 𝒪[F] G (GenericLie.adjoint 𝒪[F] p X) ∈
            cocharacterPositiveLie (CommGroupScheme.groupHom ν ≫ P.i)

end Langlands.Geometry.Building
