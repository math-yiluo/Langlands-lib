# `N(F) ∩ G(F)^♮` acts through `W(Ψ)`, from facet fixing and the split-torus product

This internal module states and proves an implication between published
propositions, at arbitrary universe `u`:

`SimplyConnectedNormalizerAffineWeylReductionStatement.{u}` is

```text
SimplyConnectedFacetFixingStatement.{u} →
  DerivedCentralSplitTorusProductStatement.{u} →
    SimplyConnectedNormalizerAffineWeylStatement.{u}
```

and `simplyConnectedNormalizerAffineWeylReduction` proves it. The conclusion is
the unchanged published range part of Kaletha–Prasad, Theorem 7.5.3(2): for
every nonarchimedean local field `F`, group scheme `G` over `F` with affine
structure morphism and `P : ParahoricBuildingData G` satisfying
`P.apartment.SatisfiesApartmentAxioms P.centralizer`, the image of
`N(F) ∩ G(F)^♮` under the apartment action is `AffineRootSystem.affineWeylGroup
P.affineRoots`.

The two premises are the only inputs of the existing derived-cover route that
have no published proof:

* `SimplyConnectedFacetFixingStatement`: for valuation building data of a simply
  connected group, a normalizer element preserving a facet of the apartment as a
  set fixes it pointwise (derived from KP 9.3.26; proof task
  `c5ad9ef0-554c-4af8-be60-3607ad0e7e9b`);
* `DerivedCentralSplitTorusProductStatement`: the product `S_D × A → S` of a
  maximal split torus of the derived group and a central split component is a
  central isogeny (proof task `52f33732-d993-43ae-aa80-b0bd915c3034`).

Neither premise mentions AS 5 for the simply connected cover, the `m(u)`-form of
AS 2 or a Tits system. The module does not prove either premise, so it does not
prove `SimplyConnectedNormalizerAffineWeylStatement`.

## The opposite-pair lemma

`ValuationBuildingData.hasOppositeFactorPairs B` proves
`RelativeRoot.HasOppositeFactorPairs B.i` for every `B : ValuationBuildingData G`
over a nonarchimedean local field: every nonidentity rational point of an actual
relative-root group has an opposite factor pair whose product normalizes the
maximal split torus. It applies the proved `rootRankOneFactorization`
(KP 2.11.17, CGP C.2.24) to the connected reductive group, maximal split torus
and embedding stored in `B`, and keeps the existence part of its unique-pair
clause. Several Library results take this predicate as an explicit hypothesis on
building data; this lemma discharges it.

## The proof of the reduction

Given the two premises, a field `F`, a group `G`, building data `P` and its
apartment axioms `hA`:

1. The simply connected cover `C` stored in `P.zeroDatum` is semisimple, hence
   connected reductive, so its structure morphism is affine; this instance is
   needed to form building data on `C`.
2. `P.derivedCoverSourceData` builds valuation building data on `C`, the forward
   normalizer map, the apartment affine equivalence, exact root transport,
   equivariance and lifts of every element of `N(F) ∩ G(F)^♮`. Its three inputs
   are the proved `simplyConnectedDerivedCoverSplitTorus`, the premise
   `DerivedCentralSplitTorusProductStatement`, and the proved
   `Cartan.centralizerValuationComparison`.
3. `DerivedCoverSourceData.normalizer_map_eq_affineWeylGroup` turns these data
   into the target equality, given the premise
   `SimplyConnectedFacetFixingStatement`, opposite factor pairs for the source
   torus in `C` and for the torus of `P`, and `hA`. Both opposite-pair inputs are
   `ValuationBuildingData.hasOppositeFactorPairs`.

## Provenance

The implication is internal: it composes published Library theorems and makes no
new literature assertion. The mathematical route is the source proof of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 7.5.3,
printed p.261 (PDF p.292), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`: transfer the simply connected
case (Theorem 7.5.1, printed pp.259–260, PDF pp.290–291) along
`G_sc(F) → G(F)^♮`. In the Library the simply connected case enters through
`SimplyConnectedFacetFixingStatement` and the transfer through
`DerivedCoverSourceData`.
