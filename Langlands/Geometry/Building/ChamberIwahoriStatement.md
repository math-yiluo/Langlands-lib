# Full chamber Iwahori decompositions

This module states the chamber and facet products for the actual full
Iwahori `I_C = P_C`, while retaining the separate sharp-group assertions.
Its entry declaration is
`ParahoricBuildingData.ChamberIwahoriDecompositionStatement`. All
declarations here are Prop-valued definitions of targets; none is a proof.

The original source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The mandatory corrections of 1 November 2024 are registered as
`kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

## Source premises

The ambient inputs are a nonarchimedean local field `F`, with
`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, an affine group scheme `G` over `F`,
and `P : ParahoricBuildingData G`. There is no characteristic, split,
quasi-split, tameness or residue-characteristic restriction.

The data `P` contain the connected-reductive structure, a maximal split
torus `i : S → G`, the actual root valuations and their apartment, and
the actual centralizer `j : Z_G(S) → G`. They also contain the data
defining `Z(F)^0` and `G(F)^0` by KP Definition 2.6.23 for the same
`i` and `j`. The valuation, equipollence, root-subgroup and normalizer
action requirements already in these published data remain in force.
The local-field scope supplies the Henselian and perfect-residue setting
of Definition 2.6.23; no assertion of existence or choice independence
of these data is made here.

The target explicitly assumes
`P.apartment.SatisfiesApartmentAxioms P.centralizer`. This is the
published fixed-apartment predicate for V6, V7, AS2–AS4 and corrected
AS5. The original Chapter 7 opening is printed pp. 235–236 / PDF
pp. 266–267; the corrections, PDF p. 33, add that AS1–AS4 hold and
AS5 is assumed. The predicate retains the relevant affine-root-system
and normalizer-image laws. Full V6 is already a field of the actual
building data. This conditional target does not supply the general
existence of such data, a complete building certificate, or a proof of
AS5.

For each `C`, `x` and `ν`, the target requires
`AffineRootSystem.IsChamber P.affineRoots C`, `x ∈ C`, and
`IsGenericCocharacter P.i ν`. The positive system consists of actual
relative roots pairing positively with `ν`. The unipotent radicals
are the actual `Dynamic.unipotent` groups for `ν` and `-ν`; genericity
selects opposite minimal parabolics. The source's chamber `C` is open
in its apartment, so `x ∈ C` retains its interior-point requirement.

The facet clause further requires
`AffineRootSystem.IsFaceOf P.affineRoots Fa C` and
`P.apartment.FacetChamberPositiveSystem Fa C ν`. The first says `Fa`
is an actual nonempty facet in the closure of `C`. The second requires
positivity on `ν` of the derivatives of affine roots vanishing on
`Fa` and positive on `C`. It expresses Fact 7.4.6's positive-system
choice, printed p. 256 / PDF p. 287, with the notation explained in
the paired Markdown of `ChamberRootProducts`.

## Full chamber conclusion

`ChamberIwahoriConclusion C x ν` packages the following conclusions:

- `I_C = P_x`, by Lemma 7.4.4(1), printed p. 256 / PDF p. 287,
  and Definition 7.4.1(4).
- `Z(F) ∩ I_C = j(Z(F)^0)`, as an equality of actual subgroups
  of `G(F)`. This is Lemma 7.4.3, printed p. 255 / PDF p. 286,
  itself the parahoric case of Lemma 7.3.16.
- The actual intersections `U^-(F) ∩ I_C` and `U^+(F) ∩ I_C`
  equal their intersections with the sharp chamber subgroup.
- Multiplication from
  `(U^-(F) ∩ I_C) × Z(F)^0 × (U^+(F) ∩ I_C)` into `G(F)`
  is injective and has range exactly `I_C`.
- For each depth `0` or `0+` and any fixed ordering within each
  sign, the ordered negative and positive block maps are injective
  with ranges respectively `U^-(F) ∩ I_C` and `U^+(F) ∩ I_C`.
  The ordered negative/full-central/positive map is injective with
  range exactly `I_C`.

Each ordered assertion quantifies over arbitrary finite indexing maps
`aneg` and `apos`, requiring injectivity and range exactly
`RelativeRoot.indivisiblePositiveRoots P.i (-ν)` and
`RelativeRoot.indivisiblePositiveRoots P.i ν`. Thus each sign lists
every nondivisible root exactly once, in arbitrary fixed order. It
does not mix the signs or assert the unrestricted all-root-order
formula added to 7.3.12 under a strictly positive central depth.
The Boolean depth is `false` for `0` and `true` for `0+`.

The imported blocks retain
`U_{a,x,r} U_{2a,x,r}`, and similarly at a facet, with trivial
second factor only when `2a` is absent. At these constant depths
V4 identifies the block with `U_{a,x,r}`; the implementation does
not delete the doubled-root factor from its definitions.

The full-parahoric conclusions are derived source targets. Corollary
7.4.9, printed p. 257 / PDF p. 288, gives the sharp products;
Proposition 7.3.12(3),(5), printed pp. 250–251 / PDF pp. 281–282,
gives their factor bijections. Definition 7.4.1(4), printed p. 255 /
PDF p. 286, adjoins `Z(F)^0`, which normalizes the root factors
because it acts trivially on the apartment under V6. Lemma 7.4.3
places the sharp central factor inside this full central factor.
The resulting negative/central/positive product has unique factors
by the algebraic open-cell injectivity used in the proof of
7.3.12(5), referring to Propositions 2.11.2(5) and 2.11.3(2),
printed p. 131 / PDF p. 162. The same uniqueness shows that adjoining the central
factor does not enlarge either unipotent intersection. This explains
the provenance of the full-intersection and full-product conclusions;
they are not additional assumptions.

## Facet conclusion and sharp assertions

`ChamberIwahoriFacetConclusion Fa C ν` has the same fixed-sign
indexing requirements. Its negative block map uses depth `0+`, its
positive block map uses depth `0`, and the central factor is the
actual `Z(F)^0`. Each sign map is injective with range the
corresponding full-Iwahori unipotent intersection; the three-factor
map is injective with range `I_C`. This follows as a source target
from the second formula of Corollary 7.4.9 and the facet comparisons
of 6.3.20–21, printed pp. 222–223 / PDF pp. 253–254, under the
retained geometric sign condition.

The entry target also includes the imported
`ChamberSharpConclusion C x ν` and, in its facet clause,
`ChamberSharpFacetConclusion Fa C x ν`. These retain
`N_x^sharp = Z_x^sharp`, both chamber depths, actual sharp
unipotent intersections, root/facet comparisons and all sharp
ordered-product bijections. Their precise content and source
premises are documented in `ChamberSharpStatement.md`. Including
them here states the sharp and full versions together without
identifying their groups or their central factors.

The corrections, PDF pp. 33–35, were checked. The proof of the added
Lemma 7.3.24, PDF p. 34, explicitly uses the full-Iwahori unipotent
intersection product with `Z(F)^0` as its central factor. Besides the Chapter 7
AS5 addition, they correct the notation after Definition 7.4.1,
the chamber in Remark 7.4.2 and the function subscript in
Lemma 7.4.4(2). None changes the product conclusions used here.

Compact openness is a separate target on the canonical rational-point
topology. This module does not assert it, prove a decomposition,
or identify this chamber Iwahori with Renard V.5.2's smaller
simultaneous normal compact-open basis.
