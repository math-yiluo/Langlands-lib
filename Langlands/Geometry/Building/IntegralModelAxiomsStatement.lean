import Langlands.Geometry.Building.FullValidity.Assignment

/-! # Integral models with Axioms 4.1.20 and 4.1.22 on supplied building data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

/-- Axioms 4.1.20 (Bruhat–Tits group schemes) and 4.1.22 (structure of the reductive quotient)
of KP on supplied data satisfying the five axioms of the corrected opening of KP Section 4.2:
for `P : ParahoricBuildingData G` over a nonarchimedean local field `F`, a polysimplicial
realization `R` and an apartment splitting `T` satisfying the seven Library predicates for
Axioms 4.1.1 (for `G` alone), 4.1.2, 4.1.4, 4.1.6 and 4.1.9, there are a family `M` of integral
models over `𝒪[F]` indexed by the non-empty bounded subsets of apartments and the facets of
`B(G)`, special-fibre quotients `Q` of its facet models and relative root reflection data `ρ`
with `M.SatisfiesModelAxioms P` (Axiom 4.1.20) and `Q.SatisfiesMorphismAxioms ρ`
(Axiom 4.1.22). No existence of `P`, `R`, `T` or of the axiom witnesses is asserted. -/
def IntegralModelAxiomsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (T : P.toValuationBuildingData.ApartmentSplitting),
    P.SatisfiesBuildingAxiom R →
    P.HasBoundedOpenStabilizers →
    P.SatisfiesAffineApartmentAxiom T →
    P.HasRootReflections →
    P.SatisfiesApartmentAxioms →
    P.HasCompatibleApartmentFacets →
    P.HasTitsSystem →
    ∃ (M : BuildingModelFamily P.toValuationBuildingData ↥𝒪[F])
      (Q : BuildingModelQuotientFamily P.toValuationBuildingData M)
      (ρ : Langlands.GroupScheme.RelativeRootReflectionData P.i),
      M.SatisfiesModelAxioms P ∧ Q.SatisfiesMorphismAxioms ρ

end Langlands.Geometry.Building
