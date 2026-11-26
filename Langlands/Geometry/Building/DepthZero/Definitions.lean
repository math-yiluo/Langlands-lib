import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.BruhatTits.IntegralModels.DepthZeroIntertwining
import Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient
import Mathlib.Basic.Complex.Basic

/-!
# Depth-zero constructions on the facets of a KP building datum

The neutral facet model supplies the parahoric. Its specified special-fibre quotient
supplies reduction, the radical preimage, and inflation. Compact induction uses the
canonical topology on the original rational-point group.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.KPBuildingDatum

open BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (D : KPBuildingDatum G) (x : BuildingFacet D.base.toValuationBuildingData)

/-- The neutral facet model's integral points, viewed in `G(F)`. -/
abbrev parahoric : Subgroup (rationalPoints G) :=
  (D.models.facetModels.model x).neutral.integralPoints

/-- The radical preimage inside the parahoric. -/
abbrev parahoricRadical : Subgroup (D.parahoric x) :=
  (D.quotients.quotient x).positivePoints.subgroupOf (D.parahoric x)

/-- The specified quotient of the neutral facet model's special fibre. -/
abbrev reductiveQuotient :
    GroupScheme (Spec (CommRingCat.of 𝓀[F])) :=
  (D.quotients.quotient x).quotient

/-- The residue-field points of the specified quotient. -/
abbrev reductiveQuotientPoints : Type u :=
  rationalPoints (D.reductiveQuotient x)

/-- The composite of reduction to the neutral special fibre and the specified projection. -/
abbrev parahoricReduction : D.parahoric x →* D.reductiveQuotientPoints x :=
  (D.quotients.quotient x).parahoricReduction

/-- The residue-field points as a finite group, using the reductivity clause of Axiom 4.1.22. -/
def finiteReductiveQuotientGroup (hD : D.SatisfiesGroupAxioms) : FiniteGrp.{u} :=
  let Q := D.quotients.quotient x
  letI : Smooth Q.quotient.X.hom := (hD.reductiveQuotients.facets.reductive_quotients x).2.2.smooth
  Q.finiteQuotientGroup

private instance genericAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- The parahoric as an open subgroup for the canonical topology on `G(F)`. -/
abbrev parahoricOpenSubgroup :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    OpenSubgroup (rationalPoints G) :=
  (D.models.facetModels.model x).localFieldIntegralOpenSubgroup

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Inflation from the residue-field points of the quotient along `parahoricReduction`. -/
abbrev depthZeroInflation (σ : Representation ℂ (D.reductiveQuotientPoints x) V) :
    Representation ℂ (D.parahoric x) V :=
  (D.quotients.quotient x).inflation σ

/-- Compact induction of `depthZeroInflation` to `G(F)` with its canonical topology. -/
abbrev depthZeroCompactInduction [LocallyOfFiniteType G.X.hom]
    (σ : Representation ℂ (D.reductiveQuotientPoints x) V) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    SmoothRep.{0, u, u} ℂ (rationalPoints G) :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  (D.quotients.quotient x).depthZeroInduction
    (D.models.facetModels.model x).localField_isOpen_congruenceSubgroup σ

end Langlands.Geometry.Building.KPBuildingDatum
