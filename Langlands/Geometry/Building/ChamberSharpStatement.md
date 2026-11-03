# Sharp chamber decompositions

Module `Langlands.Geometry.Building.ChamberSharpStatement`.
The Prop-valued target
`ValuationBuildingData.ChamberSharpDecompositionStatement` states the
fixed-apartment specialization of Kaletha–Prasad Corollary 7.4.9,
including the factor bijections of Proposition 7.3.12(3),(5).
It includes both depths `0` and `0+` and the facet-closure variant.
No proof or general existence assertion is supplied.

## Exact setting and premises

The field `F` has `[Field F] [ValuativeRel F] [TopologicalSpace F]` and
`[IsNonarchimedeanLocalField F]`. This is a specialization of Chapter 7's
Henselian discretely valued field, normalized by `ω(Fˣ) = ℤ`, and covers
both characteristics. The topology used by the apartment premises is
the canonical `rationalPointTopology F G.X`.

The parameter `B : ValuationBuildingData G` contains the actual connected
reductive group, a chosen maximal split torus `B.i : B.S.toGrp ⟶ G`,
the actual centralizer, and an `N(F)`-stable equipollence class
`B.apartment` of valuations of the root datum, with its prescribed
normalizer action and the full centralizer compatibility V 6.
The affine group scheme premise is `[IsAffineHom G.X.hom]`.
The statement additionally assumes
`B.apartment.SatisfiesApartmentAxioms B.centralizer`.
Its published fields retain V 6, V 7, the affine-root-system properties
and derivative/root identifications for `Ψ′` and `Ψ`, AS 4, and every
sentence of AS 5. The rank-zero version of the affine-root-system
predicate admits groups with no relative roots, including tori.

Chapter 7's corrected opening expressly assumes AS 5. It is therefore
retained as a premise, rather than inferred from the existence of root
valuations. The target adds no residue-characteristic, split,
quasi-split or tameness restriction. Chapter 7 does not assume perfect
residue. This target does not use the separate Chapter 5 route.

All conclusions concern the fixed apartment `A(S)`. The source's
transport between different maximal split tori does not enter these
formulas: the valuations, root subgroups, normalizer action and facets
are all those of `B.S`. The statement consequently uses the published
single-apartment axioms directly. It does not assume the later
identification of the apartment stabilizer with `N(F)`, injectivity of
the apartment map into the building quotient, or compatibility of the
building's facets. It also does not assert that the displayed data or
premises exist for every connected reductive group. The construction of
such data remains a separate obligation.

The remaining quantified premises are:

- `AffineRootSystem.IsChamber B.affineRoots C`: an actual apartment
  chamber.
- `x ∈ C`: a point in that chamber, away from every affine root
  hyperplane.
- `IsGenericCocharacter B.i ν`: the chosen positive root system.
  The actual unipotent radical is the `F`-points of
  `Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ B.i)`; replacing
  `ν` by `-ν` gives the opposite radical. Thus the chosen minimal
  parabolic is specified by the generic cocharacter.
- For the facet clause,
  `AffineRootSystem.IsFaceOf B.affineRoots F C` and
  `B.apartment.FacetChamberPositiveSystem F C ν`.
  `IsFaceOf` includes that `F` is a facet and lies in the geometric
  closure of `C`. The second premise is the required positive-system
  choice from Fact 7.4.6 and Proposition 1.3.35: the derivatives of
  affine roots vanishing on `F` and positive on `C` are positive on `ν`.
  The identification with actual roots is part of the apartment
  axioms. This is an apartment-level geometric condition.

## Chamber conclusion

`KPApartmentData.ChamberSharpConclusion` is internal notation for the
following conjunction, used under the premises above.

For every actual relative root `a`, the chamber intersection groups
`rootFixer a C` and `rootFixerPlus a C` equal the corresponding point
groups at `x`. The point groups at depths `0` and `0+` coincide.
The statement also gives `sharpNormalizer {x} = sharpCentralizer {x}`,
the equality `N_x^sharp = Z_x^sharp` in Corollary 7.4.9.
These are actual intersections with `N(F)` and `Z(F)`.

The map `sharpUnipotentProduct C x ν` multiplies an element of
`U⁻(F) ∩ sharpFixer C`, an element of `sharpCentralizer {x}`, and an
element of `U⁺(F) ∩ sharpFixer C`, in that order. It is asserted
injective, with range exactly the carrier of `sharpFixer C`.

For each `strict : Bool`, where `false` selects `0` and `true` selects
`0+`, the target quantifies over arbitrary finite enumerations `aneg`
and `apos`. Each enumeration is injective and has range exactly
`RelativeRoot.indivisiblePositiveRoots B.i (-ν)` or
`RelativeRoot.indivisiblePositiveRoots B.i ν`, respectively.
Thus every actual indivisible root of that sign occurs exactly once,
in any fixed order within its sign.

The factors are the published `chamberRootBlock`: the product of the
selected `U_a` and `U_{2a}` at the same depth, with the second factor
trivial precisely when `2a` is absent from the actual root set.
The target records that these constant-depth blocks equal their
single root groups, using the valuation's doubled-root comparison.
The explicit blocks retain the multipliable-root data of Definition
7.3.3(1); there is no convention discarding `U_{2a}` in a general
filtered block.

Each ordered sign product is injective, with range exactly the
corresponding actual unipotent/sharp intersection. The ordered
negative/central/positive product is also injective, with range exactly
`sharpFixer C`. The central factor is `sharpCentralizer {x}` at both
depths. Injectivity and exact range state a bijection onto the specified
subgroup without assuming membership of the multiplication map's
values in advance.

These are the fixed-sign bijections in Proposition 7.3.12(3),(5)
specialized to the chamber. The conclusion `N_x^sharp = Z_x^sharp`
supplies the criterion in part (5). Part (4)'s sufficient premise
`f(0) > 0` is not imposed at depth zero. The added arbitrary mixed-order
part (6) in the corrections has a strict-depth premise and is not
asserted here.

## Facet conclusion

`RootFacetConstancyConclusion` identifies `rootFixer a F` and
`rootFixerPlus a F` with their point versions at every `y ∈ F`.
This spells out the source's point-independent facet notation in
6.3.20–21. `ChamberSharpFacetConclusion` also records, for every root,
the inclusions

`U_{a,F,0+} ≤ U_{a,C,0+} ≤ U_{a,C,0} ≤ U_{a,F,0}`.

Under the required geometric sign choice, positive facet zero-depth
groups and negative facet strict-depth groups equal their chamber
groups. Each facet block retains its doubled-root factor, and the
target includes its equality with the corresponding single root group.

The sign enumerations again run over every actual indivisible root of
each sign in any fixed order. The negative facet factors have depth
`0+`, the positive facet factors have depth `0`, and the central factor
remains `sharpCentralizer {x}` for the point `x ∈ C`.
Each ordered sign product is injective with range its chamber
unipotent/sharp intersection. `orderedSharpFacetProduct` is injective
with range exactly `sharpFixer C`. This is the second formula of
Corollary 7.4.9 with its factor bijections and the comparisons of 6.3.21.

## Scope and provenance

The conclusion predicates, Boolean depth selector, and ambient-valued
multiplication maps are internal ways to express the source formulas
on the shared actual objects. The conjunction is a derived packaging
of the cited chamber statement, facet comparisons, and fixed-sign
factor bijections. There is no proof in this module.

The group here is the sharp root-generated chamber group. The full
Iwahori is `P_C`, which also uses the actual `Z(F)^0` factor. Its
definition, full product decompositions, and compact-openness are
separate targets. This statement does not identify these groups.
It also does not concern Renard V.5.2's simultaneous normal compact-open
basis.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
  SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Chapter 7 opening, printed pp. 235–236 / PDF pp. 266–267;
  Definitions 6.1.2 and 6.1.7–8; the trivial doubled-root convention
  before Definition 6.3.4, printed p. 218 / PDF p. 249;
  6.3.20–21, printed pp. 222–223 / PDF pp. 253–254;
  Definition 7.3.3(1) and Remark 7.3.4, printed p. 247 / PDF p. 278;
  Proposition 7.3.12(3),(5), printed pp. 250–251 / PDF pp. 281–282;
  Definition 7.4.1, Fact 7.4.6 and Corollary 7.4.9,
  printed pp. 255–257 / PDF pp. 286–288.
- Kaletha–Prasad, *Corrections and additions* (1 November 2024),
  registered as `kaletha-prasad-2024-corrections`,
  SHA256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  PDF pp. 33–34, corrected Chapter 7 ambient AS 5 premise and added
  strict-depth product assertion.
