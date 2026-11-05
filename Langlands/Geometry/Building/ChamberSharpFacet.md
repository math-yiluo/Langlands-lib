# Transport of sharp chamber products to facets

The module constructs equivalences from the signed facet block coordinates to
the chamber block coordinates and proves
`chamberSharpFacetConclusion_of_chamberSharpConclusion`. This derives the exact
published `ChamberSharpFacetConclusion F C x ν` from
`ChamberSharpConclusion C x ν` under the existing face and geometric
positive-system hypotheses. Every equivalence preserves the underlying rational
point, every supplied factor order, and the central factor
`sharpCentralizer {x}`.

The ambient objects are an arbitrary field `k : Type u`, actual group schemes
`S` and `G`, the monomorphism `i`, an affine `G`, and
`D : KPApartmentData i ω`. The explicit root-system assumptions are:

- Every extended affine root is an affine root or has its double in the affine
  root set (`hAS4`).
- The affine roots form `IsAffineRootSystemWithRankZero` (`hSys`).
- `C` is a chamber, `F` is a face of `C`, `x ∈ C`, and
  `FacetChamberPositiveSystem F C ν` holds.

These are existing parts of the host apartment and geometric hypotheses. The
transport requires no additional genericity premise: its coordinate families
already consist of roots with strictly positive or negative pairing. The final
theorem takes the chamber conclusion as its input; the proof of that conclusion
remains a separate obligation.

## Sources and provenance

The construction is derived from the published filtration comparisons and
ordered product definitions. Its mathematical source is the facet passage in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023):

- Lemma 6.3.20 and §6.3.21, printed pp.222–223/PDF253–254, give facet
  constancy and the inclusions and equalities between the two facet depths.
- Fact 7.4.6, printed p.256/PDF287, specifies the geometric positive-system
  condition.
- Corollary 7.4.9, printed p.257/PDF288, states the chamber and facet sharp
  products. Its final proof sentence derives the facet expression from the
  chamber expression and §6.3.21.

The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The mandatory November 1, 2024 corrections, PDF33–34, were also read:
`kaletha-prasad-2024-corrections`,
SHA256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The host statement retains the corrected AS5 hypotheses. This transport does
not prove those hypotheses or use the added arbitrary mixed-root ordering at
positive central depth.

## Implemented proof

`facetRootBlock_eq_chamberRootBlock_of_sign` applies
`chamberFacetRootFiltrationConclusion` to an actual relative root `a`.
For positive pairing it identifies the facet depth `0` group with
`rootFixer a C`; for negative pairing it identifies the facet depth `0+`
group with that same group. `chamberRootFiltrationConclusion` identifies the
chamber fixer with `filtration x a 0`. The existing block-to-group equalities
then give equality with `chamberRootBlock x false a`. Those imported
equalities account for the doubled-root factor in the original block
definitions, including the convention when the double is absent.

`facetChamberRootBlockEquiv` uses `Set.equivOfEq` on this equality.
Its coercion to `rationalPoints G` is definitionally the original point.
`facetChamberBlockCoordinatesEquiv` applies these equivalences coordinatewise
with `Equiv.piCongrRight`, without reindexing.
`orderedFacetBlockProduct_eq_chamber` is consequently a definitional equality
of the original ordered multiplication maps.

For the final theorem, the existing filtration comparison supplies the facet
constancy and comparison conjuncts. The exact enumeration-range hypotheses give
relative-root membership and the required signs for each negative and positive
coordinate. The proof selects the depth `0` ordered-product conjunct of
`ChamberSharpConclusion`, and combines the two coordinate equivalences with
the identity equivalence on `sharpCentralizer {x}`. Each facet multiplication
map is definitionally the corresponding chamber map composed with this
equivalence. Composition with an injective equivalence transports injectivity;
surjectivity of the equivalence identifies the ranges. This yields all six
ordered facet clauses with their original sharp unipotent and sharp fixer
targets.

The result proves only the chamber-to-facet implication. It supplies neither
the chamber conclusion itself nor a full Iwahori factorization with `Z(k)^0`;
the host task retains those obligations and its unchanged hypotheses.
