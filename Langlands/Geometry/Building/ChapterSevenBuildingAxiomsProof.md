# The Chapter 7 building of supplied valuation data satisfies the Section 4.2 axioms: proof

Lean module: `Langlands.Geometry.Building.ChapterSevenBuildingAxiomsProof`,
namespace `Langlands.Geometry.Building`.

## Statement

```
theorem Langlands.Geometry.Building.chapterSevenBuildingAxioms :
    ChapterSevenBuildingAxiomsStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.ChapterSevenBuildingAxiomsStatement.{u}` of the
module `Langlands.Geometry.Building.ChapterSevenBuildingAxiomsStatement`, at an
arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G),
  P.SatisfiesApartmentAxioms →
    ∃ (R : P.toValuationBuildingData.PolysimplicialRealization)
      (T : P.toValuationBuildingData.ApartmentSplitting),
      P.SatisfiesBuildingAxiom R ∧
      P.HasBoundedOpenStabilizers ∧
      P.SatisfiesAffineApartmentAxiom T ∧
      P.HasRootReflections ∧
      P.HasCompatibleApartmentFacets ∧
      P.HasTitsSystem
```

In words: for parahoric building data `P` of a group over a nonarchimedean
local field satisfying V 7 and AS 2–AS 5, the quotient
`P.toValuationBuildingData.ReducedBuilding` carries a polysimplicial
realization `R` and an apartment splitting `T` for which KP Axiom 4.1.1 (for
`G` alone), Axiom 4.1.2, Axiom 4.1.4, AS 1 and AS 6 of Axiom 4.1.6, and the
corrected Axiom 4.1.9 hold.

## Proof

The Lean proof introduces `F`, `G`, `P` and the premise `hD`, and applies

```
P.fiveAxioms_of_statements hD (actualApartmentSplitting F G P.toValuationBuildingData hD)
  affineIwahoriTits affineIwahoriTitsBuilding
```

where `ParahoricBuildingData.fiveAxioms_of_statements` (module
`Geometry.Building.RootValuationBuildingConstructionReduction`) gives, under
the apartment axioms and from an apartment splitting with (A 0)–(A 2),
`AffineIwahoriTitsStatement` and `AffineIwahoriTitsBuildingStatement`, the
seven predicates `P.SatisfiesBuildingAxiom R`, `P.HasBoundedOpenStabilizers`,
`P.SatisfiesAffineApartmentAxiom T`, `P.HasRootReflections`,
`P.SatisfiesApartmentAxioms`, `P.HasCompatibleApartmentFacets` and
`P.HasTitsSystem`. Its inputs are theorems proved in the Library without
hypotheses:

1. `actualApartmentSplitting` (module
   `Geometry.Building.ActualApartmentSplittingProof`): actual splitting data
   satisfying (A 0)–(A 2) of KP Axiom 4.1.4 for valuation building data
   satisfying the apartment axioms;
2. `affineIwahoriTits` (module `Geometry.Building.AffineIwahoriTitsProof`):
   the `G(F)^0` Iwahori–Tits system of every chamber (KP Theorem 7.5.3);
3. `affineIwahoriTitsBuilding` (module
   `Geometry.Building.AffineIwahoriTitsBuildingProof`): that Tits system is
   the Tits system of KP Axiom 4.1.9 on the quotient.

The proof then drops the conjunct `P.SatisfiesApartmentAxioms`, which is the
premise, and returns the remaining six with `R` and `T`. The statement is not
modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.chapterSevenBuildingAxioms :
  ChapterSevenBuildingAxiomsStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023):

- Chapter 4, 4.1.28, printed p. 166: where the axioms are proved for the
  Chapter 7 building. AS 1 is Proposition 6.2.1 and AS 6 holds by the
  construction of `B(G)`; Theorem 7.5.3 constructs the Iwahori–Tits system and
  verifies the first part of Axiom 4.1.9; Definition 7.6.1 gives Axiom 4.1.1
  except the bijection between maximal split tori and apartments, which is
  Proposition 7.6.3; Corollary 7.3.14 and Propositions 7.6.4, 7.7.1 and 7.7.5
  give Axiom 4.1.2 and the second part of Axiom 4.1.9.
- Chapter 7, §7.6, Remark 7.6.5, printed p. 266: Proposition 7.6.4 completes
  the proof of Axioms 4.1.1, 4.1.4 and 4.1.9.

The authors' *Corrections and additions* (version of 1 November 2024), p. 33,
add AS 5 to the opening assumptions of Chapter 7. The Lean statement assumes
V 7 in addition and covers nonarchimedean local fields, as described on the
statement's page.
