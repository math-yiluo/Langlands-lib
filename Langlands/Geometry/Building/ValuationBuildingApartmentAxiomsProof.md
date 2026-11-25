# The apartment axioms for every compatible valuation class: proof

Lean module: `Langlands.Geometry.Building.ValuationBuildingApartmentAxiomsProof`,
namespace `Langlands.Geometry.Building`.

## Statement

```
theorem Langlands.Geometry.Building.valuationBuildingApartmentAxioms :
    ValuationBuildingApartmentAxiomsStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.ValuationBuildingApartmentAxiomsStatement.{u}` of
the module `Langlands.Geometry.Building.UnramifiedValuationDescentStatement`,
at an arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G), B.SatisfiesApartmentAxioms
```

In words: for every nonarchimedean local field `F` and every affine group `G`
over `F`, every `B : ValuationBuildingData G` (connected reductivity, a maximal
split torus, an `N(F)`-stable equipollence class of compatible valuations of
its root datum, the actual centralizer, and V 6) satisfies V 7 and AS 2–AS 5,
the latter in the corrected form with its three sentences.

## Proof

The Lean proof is the single application

```
valuationBuildingApartmentAxioms_of_facetFixing simplyConnectedFacetFixing
```

of `valuationBuildingApartmentAxioms_of_facetFixing` (module
`Geometry.Building.ValuationBuildingApartmentAxiomsAssembly`), which derives
the statement from `SimplyConnectedFacetFixingStatement.{u}`, to
`simplyConnectedFacetFixing` (module
`Geometry.Building.SimplyConnectedFacetFixingProof`), proved without
hypotheses: for valuation building data of a simply connected group, every
point of the normalizer preserving an apartment facet fixes it pointwise.

The assembly fills each axiom from a theorem of the Library; the facet-fixing
statement gives the simply connected sentence of AS 5. The details are on the
page of `Geometry.Building.ValuationBuildingApartmentAxiomsAssembly`. The
statement is not modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.valuationBuildingApartmentAxioms :
  ValuationBuildingApartmentAxiomsStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Chapter 9: §9.5, printed pp. 363–364, completes the proof of Axiom 4.1.6 for
the descended building (AS 2 and AS 3 by Proposition 9.4.19, AS 4 by
Proposition 9.4.18, AS 5 by Proposition 9.4.35); §9.6.6, printed p. 367,
compares the two building constructions. The statement quantifies over every
compatible class, which by the uniqueness of KP Proposition 6.2.6 is the class
of Theorem 9.6.5; see the page of
`Geometry.Building.UnramifiedValuationDescentStatement`. The Lean proof
follows a different route, described on the page of the assembly.
