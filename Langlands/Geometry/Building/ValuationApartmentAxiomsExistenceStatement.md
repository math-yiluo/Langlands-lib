# Existence of actual valuation data satisfying the Chapter 7 apartment axioms

`Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement.{u}` is a
named Prop-valued `def` at an arbitrary universe `u`. It is a proof target, not a
theorem. It asserts that the material of Kaletha–Prasad Chapters 6 and 7 is available
for every connected reductive group over a nonarchimedean local field: some actual
valuation-building datum exists and satisfies the apartment axioms that Chapter 7
assumes.

## Statement

```text
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  ∃ B : ValuationBuildingData G, B.SatisfiesApartmentAxioms
```

The field, group, connected-reductivity hypothesis and `IsAffineHom` instance are
introduced exactly as in the published `RootValuationBuildingConstructionStatement`.
The witness is a datum of the existing structure `ValuationBuildingData G`, which
bundles

- a maximal split torus `i : S → G` (`IsMaximalSplitTorus`);
- an `N(F)`-stable equipollence class `A(S)` of valuations of the root datum of
  `(G, S)`, normalized by `ω = ord_F` (`KPApartmentData i (localFieldOrder F)`,
  KP Definitions 6.1.2 and 6.1.7, with the `N(F)`-action of 6.1.8);
- the actual centralizer `Z = Z_G(S)` (`CentralizerDatum i`);
- axiom V 6 (`ω`-compatibility) of KP Definition 6.1.2 on all of `Z(F)`.

`B.SatisfiesApartmentAxioms` is the existing abbreviation for
`B.apartment.SatisfiesApartmentAxioms B.centralizer`. Its fields are V 6 again, V 7
of KP Definition 6.1.2 for the canonical topology `rationalPointTopology F G.X`,
AS 2 and AS 3 (the sets `Ψ′` and `Ψ` of the class are affine root systems with
derivative set `Φ`), AS 4 (for `ψ ∈ Ψ′` one of `ψ`, `2ψ` lies in `Ψ`), and the three
sentences of AS 5 for the image of `N(F)` in the affine automorphisms of `A(S)`:
`W(Ψ) ⊆ image ⊆ W(Ψ)ᵉˣᵗ`, equality with `W(Ψ)` when `G` is simply connected, and
equality with `W(Ψ)ᵉˣᵗ` when `G` is quasi-split and adjoint.

Nothing about the reduced building, the polysimplicial structure, `G(F)^0` or a Tits
system is asserted. AS 1 and AS 6 are not fields of the predicate; the Library proves
AS 1 for every datum (`rootReflection`) and AS 6 from these axioms together with the
proved rank-one factorization (`hasCompatibleApartmentFacets_of_rankOne`,
`rootRankOneFactorization`).

## Source correspondence

The source is *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, read with the
corrections of 1 November 2024, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

- Definition 6.1.2 (printed p. 199 / PDF p. 230) defines valuations of the root
  datum with V 0–V 5, `ω`-compatibility V 6 and topology compatibility V 7.
- The opening of §9.6 (printed pp. 364–365 / PDF pp. 395–396) states that for
  non-quasi-split groups the material of Chapters 6 and 7 was conditional on the
  existence of valuations of root data, and that §9.6 supplies, for every connected
  reductive `G` and maximal split torus `S`, a canonical equipollence class.
- Theorem 9.6.5 (printed pp. 366–367 / PDF pp. 397–398): for `x ∈ A`, the functions
  `ϕ^x` of Construction 9.6.1 form a valuation of the root datum compatible with `ω`;
  `x ↦ ϕ^x` is `V(S) ⋊ N(k)`-equivariant and its image is an equipollence class.
- 9.6.6 (printed p. 367 / PDF p. 398) identifies the affine root systems `Ψ` and `Ψ′`
  of Definition 6.3.4 for this class with those of 9.4.12, under the isomorphism
  `z ↦ ϕ^z` of apartments.
- §9.5 (printed pp. 363–364 / PDF pp. 394–395) records where Axiom 4.1.6 is proved
  for the descended building: AS 2 and AS 3 in Proposition 9.4.19, AS 4 in
  Proposition 9.4.18, AS 5 in Proposition 9.4.35. Through 9.6.6 these become AS 2–AS 5
  for the class of Theorem 9.6.5. For V 7, Construction 9.6.1 (PDF p. 396)
  identifies the filtration subgroups `U_{a,x,r}` of `ϕ^x` with the bounded affine
  root groups `U_ψ`, and the remark after Definition 6.1.2 (PDF p. 230) states that
  all valuations constructed in the book have V 6 and V 7.
- 4.1.28 (printed p. 166 / PDF p. 197): "once the availability of valuations of
  root data is established in §9.6, the material of Chapters 6 and 7 becomes
  available for non-quasi-split groups as well."
- Corrections, Chapter 7 (PDF p. 33): Chapter 7 assumes AS 5 in addition to
  AS 1–AS 4; for general `G` this amounts to the simply connected sentence, which
  "is proved in this generality in Proposition 9.4.35, assuming that the residue
  field of k is perfect". The residue field of a nonarchimedean local field is
  finite, hence perfect.

The statement asks for some maximal split torus with some class. KP's class is
canonical and exists for every maximal split torus; existence for one torus is the
weaker assertion, and by conjugacy of maximal split tori it determines the others.

## Scope

This is the existence half of the construction targeted by
`RootValuationBuildingConstructionStatement`: projecting that statement's witness `P`
to `P.toValuationBuildingData` and its `P.SatisfiesApartmentAxioms` field gives this
statement. It is the input that makes the Chapter 7 conditional results
(`AffineIwahoriTitsStatement` and the results on supplied `ParahoricBuildingData`)
unconditional. No universe, characteristic, rank, split, quasi-split, tameness or
residue-size restriction is imposed. No metric, integral model, descent datum,
canonical-model comparison or uniqueness of the class is asserted.
