# Actual root-valuation data with the metric-construction axioms: proof

Lean module: `Langlands.Geometry.Building.RootValuationBuildingConstructionProof`,
namespace `Langlands.Geometry.Building`.

## Statement

```
theorem Langlands.Geometry.Building.rootValuationBuildingConstruction :
    RootValuationBuildingConstructionStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.RootValuationBuildingConstructionStatement.{u}` of
the module `Langlands.Geometry.Building.RootValuationBuildingConstructionStatement`,
at an arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  ∃ (P : ParahoricBuildingData G)
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (T : P.toValuationBuildingData.ApartmentSplitting),
    P.SatisfiesBuildingAxiom R ∧
    P.HasBoundedOpenStabilizers ∧
    P.SatisfiesAffineApartmentAxiom T ∧
    P.HasRootReflections ∧
    P.SatisfiesApartmentAxioms ∧
    P.HasCompatibleApartmentFacets ∧
    P.HasTitsSystem
```

In words: for every connected reductive group `G` over a nonarchimedean local
field `F` there are parahoric building data `P`, a polysimplicial realization
`R` and an apartment splitting `T` of the root-valuation quotient of `P` such
that the quotient satisfies the building clauses of KP Axiom 4.1.1, Axiom
4.1.2 (bounded open stabilizers), Axiom 4.1.4 (affine apartments), Axiom 4.1.6
(AS 1–AS 6, with V 7) and Axiom 4.1.9 (the Tits system).

## Proof

The Lean proof is the single application

```
rootValuationBuildingConstructionReduction valuationApartmentAxiomsExistence
  actualApartmentSplitting affineIwahoriTits affineIwahoriTitsBuilding
```

of `rootValuationBuildingConstructionReduction` (module
`Geometry.Building.RootValuationBuildingConstructionReduction`), whose type
`RootValuationBuildingConstructionReductionStatement.{u}` is the implication
from four statements to the target. Each is discharged by a theorem proved in
the Library without hypotheses:

1. `valuationApartmentAxiomsExistence` (module
   `Geometry.Building.ValuationApartmentAxiomsExistenceProof`): valuation
   building data satisfying the apartment axioms exist.
2. `actualApartmentSplitting` (module
   `Geometry.Building.ActualApartmentSplittingProof`): such data have actual
   splitting data satisfying (A 0)–(A 2) of KP Axiom 4.1.4.
3. `affineIwahoriTits` (module `Geometry.Building.AffineIwahoriTitsProof`):
   the `G(F)^0` Iwahori–Tits system of every chamber (KP Theorem 7.5.3).
4. `affineIwahoriTitsBuilding` (module
   `Geometry.Building.AffineIwahoriTitsBuildingProof`): that Tits system is the
   Tits system of KP Axiom 4.1.9 on the quotient.

Inside the reduction, the data of the first statement are extended to
parahoric building data (`ParahoricBuildingData.exists_toValuationBuildingData_eq`)
and `ParahoricBuildingData.fiveAxioms_of_statements` derives the seven
predicates; the details are on the page of
`Geometry.Building.RootValuationBuildingConstructionReduction`. The statement
is not modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.rootValuationBuildingConstruction :
  RootValuationBuildingConstructionStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Chapter 9: Theorem 9.2.7, printed p. 329, the descended set `B(G_K)^Γ` with its
apartments and polysimplicial structure is a building on which `G(k)` acts by
polysimplicial isometries; §9.5, printed pp. 363–364, the axioms for the
descended building; Theorem 9.6.5, printed p. 366, and §9.6.6, printed p. 367,
the compatible valuation class and the comparison of the two building
constructions. The Lean statement keeps the five axioms listed above, on the
quotient built from valuation data, as described on the statement's page. The
authors' *Corrections and additions* (version of 1 November 2024), p. 33, add
AS 5 to the opening assumptions of Chapter 7.
