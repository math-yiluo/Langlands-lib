import Langlands.Geometry.Building.KPMinimalCongruentCentralizer
import Langlands.Geometry.Building.IntegerValuationBuildingComparison
import Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement
import Langlands.Geometry.Building.KPWeaklyInducedTorus

/-! # Properties of the minimal congruent centralizer filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

namespace MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]

/-- Two apartment coordinates represent the same reduced building point.
An inner isomorphism transports the apartments, and its rational conjugating
element is canceled in the target reduced building. -/
def IsSameBuildingPoint (B B' : BuildingData F H) (x : B.Apartment) (x' : B'.Apartment) : Prop :=
  ∃ (g : rationalPoints H) (e : B.S ≅ B'.S)
    (he : B.i ≫ (H.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ B'.i),
    B.buildingComparison B' e (H.innerIso g) he (B.apartmentMap x) = g • B'.apartmentMap x'

end MaximalUnramified.BuildingData

/-- The order properties needed to package the constructed §9.8 subgroups. -/
def MinimalCongruentCentralizerOrderStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.MinimalCongruentCentralizerOrder

/-- KP Lemma 9.8.1 at zero depth, for the constructed subgroups. -/
def MinimalCongruentCentralizerZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G),
    P.minimalCongruentCentralizerPoints 0 = P.centralizerZero

/-- KP Propositions 7.3.17 and 7.6.4: changing between apartment presentations of
the same point over `K` gives equality of the actual subgroups of `H(K)`. -/
def MinimalCongruentMoyPrasadApartmentIndependenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffineHom H.X.hom]
    (B B' : MaximalUnramified.BuildingData F H)
    (hT : IsTorus B.centralizer.Z) (hT' : IsTorus B'.centralizer.Z)
    (x : B.Apartment) (x' : B'.Apartment),
    B.IsSameBuildingPoint B' x x' →
      ∀ r : ℝ≥0, B.minimalCongruentMoyPrasad hT x r = B'.minimalCongruentMoyPrasad hT' x' r

/-- KP §9.8: any special-torus lift of the unique centralizer building point
computes the same subgroup of `Z(F)`. -/
def MinimalCongruentCentralizerIndependenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    (t : P.centralizerParahoricBuilding.UnramifiedComparisonTorus) (L : t.ApartmentLift),
    ∀ r : ℝ≥0, P.minimalCongruentCentralizerPointsOfLift L r =
      P.minimalCongruentCentralizerPoints r

/-- The four existing filtration axioms for the subgroups constructed in §9.8. -/
def MinimalCongruentCentralizerAxiomsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ h : P.MinimalCongruentCentralizerOrder,
      (P.minimalCongruentCentralizerFiltration h).SatisfiesFiltrationAxioms

/-- Every finite-depth centralizer subgroup is open in `Z(F)`. -/
def MinimalCongruentCentralizerOpenStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G),
    ∀ h : P.MinimalCongruentCentralizerOrder,
      (P.minimalCongruentCentralizerFiltration h).IsOpenFiltration

/-- The sharper positive-depth bound for the centralizer component of pairs
involving a double root. This is the hypothesis of the double-root forms of
KP Proposition 13.2.5(1), (2), and (4). -/
def MinimalCongruentCentralizerDoubleRootStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ h : P.MinimalCongruentCentralizerOrder,
      (P.minimalCongruentCentralizerFiltration h).IsDoubleRootCommutatorFriendly

/-- KP Corollary B.10.13 and §9.8: for a weakly induced maximally split maximal
torus of `Z_K`, the standard construction gives the same centralizer subgroups. -/
def MinimalCongruentCentralizerWeaklyInducedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    (t : P.centralizerParahoricBuilding.UnramifiedComparisonTorus) (L : t.ApartmentLift),
    IsWeaklyInducedTorus F (L.buildingData.centralizerTorus L.centralizer_isTorus) →
      ∀ r : ℝ≥0, P.minimalCongruentCentralizerPoints r =
        (L.buildingData.moyPrasad L.centralizer_isTorus
          (L.e P.centralizerBuildingPoint) r).comap
            (rationalExtend F (UnramifiedClosure F) P.centralizer.Z)

/-- The same comparison with the standard filtration computed by taking the
centralizer term of a rational Moy–Prasad family in the ambient group. -/
def MinimalCongruentStandardCentralizerComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ (t : P.centralizerParahoricBuilding.UnramifiedComparisonTorus) (L : t.ApartmentLift),
      IsWeaklyInducedTorus F (L.buildingData.centralizerTorus L.centralizer_isTorus) →
    ∀ (tG : P.UnramifiedComparisonTorus) (LG : tG.ApartmentLift) (x : P.Apartment) (r : ℝ≥0),
      P.minimalCongruentCentralizerPoints r =
        ((LG.buildingData.moyPrasad LG.centralizer_isTorus (LG.e x) r).comap
          (rationalExtend F (UnramifiedClosure F) G)).comap
            (rationalPoints.map P.centralizer.j)

/-- The properties of the constructed centralizer filtration used for the
constant-depth Moy–Prasad groups. -/
def MinimalCongruentCentralizerStatements : Prop :=
  MinimalCongruentCentralizerOrderStatement.{u} ∧
  MinimalCongruentCentralizerZeroStatement.{u} ∧
  MinimalCongruentMoyPrasadApartmentIndependenceStatement.{u} ∧
  MinimalCongruentCentralizerIndependenceStatement.{u} ∧
  MinimalCongruentCentralizerAxiomsStatement.{u} ∧
  MinimalCongruentCentralizerOpenStatement.{u} ∧
  MinimalCongruentCentralizerDoubleRootStatement.{u} ∧
  MinimalCongruentCentralizerWeaklyInducedStatement.{u} ∧
  MinimalCongruentStandardCentralizerComparisonStatement.{u}

end Langlands.Geometry.Building
