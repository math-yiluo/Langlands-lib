# Chamber and facet root-product maps

This module defines the multiplication maps used in the chamber and facet
formulas of Kaletha–Prasad Corollary 7.4.9. It uses the actual root-group
filtrations and sharp fixers of `KPApartment`, `KPBuilding` and
`KPRootFixerPlus`. All declarations are in
`Langlands.Geometry.Building.KPApartmentData`.

The input is `D : KPApartmentData i ω`, for a field `k`, commutative group
scheme `S`, group scheme `G`, and a morphism `i : S.toGrp ⟶ G` with
`Mono i.hom.hom.left` and `IsAffineHom G.X.hom`. No reductive, local-field,
chamber or facet hypothesis is needed to define the maps. Their intended
structural application requires those additional source hypotheses; this
module asserts no decomposition, injectivity or range equality.

## Point blocks and multiplication

The Boolean `strict` selects exactly two depths: `false` means `0` and
`true` means `0+`.

- `chamberRootGroup D x strict a` is `D.filtration x a 0` or
  `D.filtrationPlus x a 0`, according to that choice.
- `chamberRootBlock D x strict a` is the set product of the chosen
  `a`-filtration and the chosen `2 • a`-filtration. The second factor is
  the trivial subgroup exactly when `2 • a ∉ relativeRoots i`.
  At depth `0`, this reuses the published `D.filtrationBlock x (fun _ => 0) a`.
  At depth `0+`, it is the same two-factor expression using
  `D.filtrationPlus` at `0`.
- `orderedChamberBlockProduct D x strict a` multiplies a dependent
  family of block elements indexed by `j : Fin n`, by
  `(List.ofFn fun j => (u j : rationalPoints G)).prod`.

The block is a set of products in `G(k)`, not a pair of independently
chosen factors. Its subtype elements therefore do not retain a possibly
nonunique presentation inside `U_a U_{2a}`. The definition retains the
doubled-root factor. Its collapse to the first subgroup at these constant
depths is a separate structural assertion.

`orderedSharpChamberProduct D x strict aneg apos` multiplies the
negative block family, an element of `D.sharpCentralizer {x}`, and the
positive block family, in that order. Both choices of `strict` use the
same central factor. The lists are arbitrary at definition time. Later
fixed-sign bijection targets require each list to enumerate exactly once
all actual indivisible roots of its sign. No arbitrary interleaving of
the two signs is implicit.

## Actual unipotent intersections

`sharpUnipotentPoints D ν Ω` is literally

`(Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier
(Over.mk (𝟙 _)) ⊓ D.sharpFixer Ω`.

Thus its first factor is the field-valued points of the actual Dynamic
unipotent subgroup, evaluated on the identity test scheme, and its second
factor is the actual sharp fixer. For a generic cocharacter in the
intended connected reductive, maximal split torus scope, this is the
minimal-parabolic unipotent intersection used in Proposition 7.3.12.
No comparison with that source characterization is proved here.

`sharpUnipotentProduct D C x ν` maps the product of these intersections
for `-ν` and `ν`, with `D.sharpCentralizer {x}` between them, into
`rationalPoints G` by multiplication. The definition permits arbitrary
`C` and `x`; the chamber formula later requires `C` to be an actual
apartment chamber and `x ∈ C`.

## Facet sign choice and multiplication

`FacetChamberPositiveSystem D F C ν : Prop` says that every
`ψ ∈ D.affineRoots` which vanishes at every point of `F` and is
strictly positive at every point of `C` has derivative `rootForm i a`
for some actual relative root `a` with `0 < latticePairing S a ν`.
Under the source's derivative/root identification, a facet `F` in the
closure of a chamber `C`, and a generic `ν`, this is exactly the condition
`∇Ψ_F(C)^+ ⊆ Φ^+` in Fact 7.4.6. Here it is a geometric predicate
definition, with no assertion that a suitable `ν` exists.

`facetRootGroup D F strict a` selects the actual intersection
`D.rootFixer a F` or `D.rootFixerPlus a F`. These are the published
intersections of the point groups over `F`, with the actual root group
included; for the empty set they equal that root group. They are defined
for arbitrary `F`. Their comparison with the point-independent facet
notation of §6.3.20–21 is a separate statement requiring an actual facet.

`facetRootBlock D F strict a` is the set product of the selected
intersection for `a` and the selected intersection for `2 • a`, with the
same absent-root convention. `orderedFacetBlockProduct` multiplies a
`Fin n` family of elements of these sets in order. Finally,
`orderedSharpFacetProduct D F x aneg apos` uses the negative blocks at
`0+`, then `D.sharpCentralizer {x}`, then the positive blocks at `0`.
In the intended facet formula `x` belongs to the chamber `C`, so the
central group is still the chamber-interior one.

## Provenance and boundary

The blocks specialize Definition 7.3.3(1) at constant depths `0` and
`0+`; the absent-doubled-root convention is the one preceding
Definition 6.3.4. The intersections, Boolean selector and ordered maps are
internal notation for the actual multiplication maps in Proposition
7.3.12(3),(5) and Corollary 7.4.9. The sign predicate spells out the
geometric condition in Fact 7.4.6 using actual derivatives and pairings.

This module supplies no complete corrected Chapter 7 ambient predicate,
root-fixer constancy, factor bijection, sharp-normalizer equality, full
parahoric or central Iwahori. It asserts no building existence or
compact-openness. In particular `KPApartmentData` alone does not supply
full V6/V7, the equivariant apartment family or AS5, and no sharp fixer is
identified with a full parahoric.

Sources:

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  convention preceding Definition 6.3.4, printed p. 218 / PDF p. 249;
  §6.3.20–21, printed pp. 222–223 / PDF pp. 253–254;
  Definition 7.3.3(1) and Remark 7.3.4, printed p. 247 / PDF p. 278;
  Proposition 7.3.12(3),(5), printed pp. 250–251 / PDF pp. 281–282;
  Definition 7.4.1, Fact 7.4.6 and Corollary 7.4.9, printed
  pp. 255–257 / PDF pp. 286–288.
- Kaletha–Prasad, *Corrections and additions* (1 November 2024),
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
  PDF pp. 33–34: corrected Chapter 7 scope and the added strict-depth
  product assertion. No such structural assertion is made here.
