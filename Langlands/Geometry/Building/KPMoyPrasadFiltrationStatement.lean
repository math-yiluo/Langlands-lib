import Langlands.Geometry.Building.KPMoyPrasadFiltration
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness

/-!
# KP Proposition 13.2.5 (1), (2), (4) and openness on supplied data

Four targets for the Moy–Prasad subgroups `P_{x,r}` of supplied building data and a supplied
filtration of `Z(F)` with the properties of KP §9.8.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

/-- The filtration `(P_{x,r})_{r ≥ 0}` is separated: `⋂_r P_{x,r} = {1}` (KP Proposition 13.2.5,
opening sentence). -/
def MoyPrasadSeparatedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration),
    P.SatisfiesApartmentAxioms → Zf.SatisfiesFiltrationAxioms →
      ∀ x : P.Apartment, ⨅ r, Zf.moyPrasad x r = ⊥

/-- At every finite depth `r ≥ 0`, `P_{x,r}` is open and bounded in `G(F)` (KP Proposition 13.2.5,
opening sentence, restricted to finite depths). -/
def MoyPrasadBoundedOpenStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration),
    P.SatisfiesApartmentAxioms → Zf.SatisfiesFiltrationAxioms → Zf.IsOpenFiltration →
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      ∀ (x : P.Apartment) (r : NNReal),
        IsOpen (Zf.moyPrasad x r : Set (rationalPoints G)) ∧
          IsAlgebraicallyBounded F G.X (Zf.moyPrasad x r : Set (rationalPoints G))

/-- The Moy–Prasad subgroup of a point of the reduced building is well defined: any two
presentations `g P_{x,r} g⁻¹` with `g · x = y` agree. This is KP Proposition 13.2.5(1) and (2)
for supplied data: other apartments are `G(F)`-translates of `A(S)`, and `IsMoyPrasadAt` is
covariant by construction (`IsMoyPrasadAt.smul`). -/
def MoyPrasadCovarianceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration),
    P.SatisfiesApartmentAxioms → Zf.SatisfiesFiltrationAxioms →
      ∀ (y : P.ReducedBuilding) (r : NNReal) (Q Q' : Subgroup (rationalPoints G)),
        Zf.IsMoyPrasadAt y r Q → Zf.IsMoyPrasadAt y r Q' → Q = Q'

/-- `[P_{x,r}, P_{x,s}] ⊆ P_{x,r+s}` (KP Proposition 13.2.5(4)). -/
def MoyPrasadCommutatorStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration),
    P.SatisfiesApartmentAxioms → Zf.SatisfiesFiltrationAxioms →
      ∀ (x : P.Apartment) (r s : NNReal),
        ⁅Zf.moyPrasad x r, Zf.moyPrasad x s⁆ ≤ Zf.moyPrasad x (r + s)

/-- The four targets together: KP Proposition 13.2.5 (opening sentence at finite depths, (1),
(2) and (4)) for supplied data. Parts (3), (5) and (6) are not included. -/
def MoyPrasadFiltrationStatement : Prop :=
  MoyPrasadSeparatedStatement.{u} ∧ MoyPrasadBoundedOpenStatement.{u} ∧
    MoyPrasadCovarianceStatement.{u} ∧ MoyPrasadCommutatorStatement.{u}

end Langlands.Geometry.Building
