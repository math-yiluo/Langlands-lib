# The chamber Iwahori decompositions from their algebraic prerequisites

This derived, internal unit assembles published and staged results into a
reduction of the chamber Iwahori target
`ParahoricBuildingData.ChamberIwahoriDecompositionStatement` to three named
statements:

- `RelativeRoot.DynamicRootOrderedProductStatement`, the ordered relative-root
  products onto the Dynamic unipotent radicals;
- `RootRankOneFactorizationStatement`, the opposite factor pairs of Kaletha–Prasad
  Proposition 2.11.17;
- `P.CentralizerParahoricIntersectionStatement`, Kaletha–Prasad Lemma 7.4.3
  (`Z(F) ∩ G(F)^0_Ω = Z(F)^0`).

It proves none of the three. Each is the target of a separate proof task.

## Statement

`ChamberIwahoriPrerequisiteReductionStatement` says the following. Assume
`RelativeRoot.DynamicRootOrderedProductStatement.{u}` and
`RootRankOneFactorizationStatement.{u}`. Take a nonarchimedean local field `F`
in universe `u`, a group scheme `G` over `Spec F` with affine structure
morphism, and an actual parahoric building datum `P : ParahoricBuildingData G`.
Then `P.CentralizerParahoricIntersectionStatement` implies
`P.ChamberIwahoriDecompositionStatement`. The theorem
`chamberIwahoriPrerequisiteReduction` proves it.

The intermediate theorem
`ValuationBuildingData.chamberSharpDecomposition_of_prerequisites` proves
`B.ChamberSharpDecompositionStatement` for every actual valuation building
datum `B` from the first two statements alone. This is the sharp chamber
decomposition: Kaletha–Prasad Corollary 7.4.9 with the bijections of
Proposition 7.3.12(3),(5).

## Proof

*Sharp decomposition.* Let `B` be a valuation building datum whose apartment
satisfies `SatisfiesApartmentAxioms`. Let `C` be a chamber, `x ∈ C`, and `ν`
a generic cocharacter. The premises of the helper theorems come from `B` as
follows.

- `S` is a split torus: the first component of `IsMaximalSplitTorus`.
- The relative roots are finite: `IsSplitTorus.finite_relativeRoots`, which
  uses local finite type of `G`, a consequence of the smoothness in
  `IsConnectedReductive`.
- Relative roots and restricted characters span: the unconditional
  `relativeRootsRestrictedCharactersSpan`.
- Opposite factor pairs: the assumed `RootRankOneFactorizationStatement`.
- AS 2 for `Ψ′` with derivative `Φ`, AS 3 for `Ψ`, and AS 4: the fields of
  `SatisfiesApartmentAxioms`.

`KPApartmentData.sharpFixer_subset_mul_of_mem_chamber` (module
`ChamberExchange`) then gives, for every generic `mu`,
`G(F)^♯_x ⊆ X_x(Φ_{-mu}) · X_x(Φ_mu) · Z(F)^♯_x`. With the assumed
`DynamicRootOrderedProductStatement`, `KPApartmentData.chamberSharpConclusion_of_core`
(module `ChamberSharpCore`) turns this inclusion into
`ChamberSharpConclusion C x ν`. The facet part
`ChamberSharpFacetConclusion F C x ν` follows for every face `F` of `C` that
satisfies `FacetChamberPositiveSystem F C ν`. It comes from
`chamberSharpFacetConclusion_of_chamberSharpConclusion` (module
`ChamberSharpFacet`).

*Full decomposition.* For a parahoric building datum `P`, apply the published
`chamberIwahoriReduction` (module `ChamberIwahoriReduction`). Its inputs are
the sharp decomposition of `P.toValuationBuildingData` from the previous step
and the assumed centralizer intersection of `P`.

## Provenance

The source route is Kaletha–Prasad Proposition 7.3.12 (printed pp. 250–251,
PDF pp. 281–282) and Corollary 7.4.9 (PDF pp. 287–288). The full step follows
Lemma 7.4.3 (PDF p. 286), as recorded in `ChamberIwahoriReduction`. This
module only composes the cited Lean results and adds no new mathematics. The
derivation of the finiteness, splitness and spanning premises from the actual
group data is internal.
