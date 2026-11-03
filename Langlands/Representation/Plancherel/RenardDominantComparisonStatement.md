# Actual dominant centralizer sections and positive covers

Author: Worker 454. The unchanged centralizer-valuation helper modules were
authored by Worker 1266.

This is a statement unit for every actual nonarchimedean local field `F`,
in mixed or equal characteristic. Let `G` be an actual connected reductive
group scheme, let `i : S → G` be a maximal split torus, and let `ν` be an
actual cocharacter pairing nontrivially with every relative root. The
positive relative roots are exactly `positiveRelativeRoots i ν`. Let
`j : Z → G` be a closed subgroup representing the actual algebraic
centralizer `torusCentralizer i`, with `s : S → Z` and `s ≫ j = i`.
The affine instance on `G` is explicit for the root constructions;
connected reductivity supplies this property.

As in `CentralizerValuation`, `h` is an explicit bijectivity argument for
the actual restriction-evaluation map. Its general existence is the
separate `CentralizerValuationComparisonStatement`. Here the conclusions
are required for every such argument. The actual-centralizer structural
comparison, including connected reductivity of `Z` and the
split-component property of `s`, is needed to apply the separate
split-component lattice statements. Neither property nor any desired
finite-index conclusion is hidden in the definition of the image.

`RenardDominantComparisonStatement` imposes these actual-group hypotheses
and concludes `DominantCentralizerLatticeConclusions i ν s h`. The latter
is a proposition packaging the seven conclusions below; it is not a
structure of assumed Cartan or representative properties.

## Normalization and the two actual image realizations

Write `ω = centralizerValuation s h` and `D = dominantCentralizer i ν s h`.
The normalization is positive character order:
`χ(ω(z)) = v_F(χ(z))`. Thus `D` is given by
`α(ω(z)) ≥ 0` for every chosen positive relative root. The uniformizer has
order `+1`.

The first conclusion says that the actual point obtained by evaluating
an actual cocharacter `c` at that uniformizer and mapping along `s` has
valuation `1 ⊗ c` in the real cocharacter space. The second identifies
the already defined `C0Plus` with the intersection `C0 ∩ D`. Together
these compare its nonnegative integer root pairings with the actual
centralizer chamber, without parametrizing every centralizer valuation
by an integral cocharacter.

The third conclusion identifies the two realizations of the chamber:
`centralizerValuationImageEquiv s h` maps `dominantValuationImage i ν s h`
onto the image of `D` under the range-restricted integer
`rationalCharacterValuation Z`. Both ambient groups are actual valuation
ranges. No equality with a full integral cocharacter lattice is stated.
The chamber is a set in a range, rather than a subgroup.

## Full transversals and dominant sections

The fourth conclusion asserts the existence of a finite full-lattice
transversal `F0` lying in `D`. Full transversality means exactly one actual
point for each class in the quotient of the actual integer valuation
image by `splitValuationImage s`. It does not mean that `F0` represents
every dominant valuation by itself.

The fifth conclusion applies to every full transversal, including ones
whose elements are not all dominant. Its product `C0 F0` is cut by the
actual chamber:

`tildeC0Plus s F0 D = (C0 S s * F0) ∩ D`.

This set is a dominant valuation section: its points lie in `D` and
biject onto the image of `D` under the integer valuation. The statement
also explicitly requires a bijection under the range-restricted `ω`
onto `dominantValuationImage i ν s h`. Consequently both actual image
realizations use the same representatives. Intersecting with the
chamber preserves the section property because dominance depends only
on the valuation; positivity of the original `F0` is unnecessary for
this conclusion.

## Positive products and repetition

The sixth conclusion asserts that some finite positive product cover
`Fcover` exists. In the imported predicate this means that `Fcover` is
finite and contained in `D`, the product `C0Plus * Fcover` remains in
`D`, and its integer valuation image covers the image of `D`. Repeated
residue classes in `Fcover` and repeated valuation classes among the
product pairs are permitted. This conclusion is a covering assertion.

The seventh conclusion is conditional on the separate predicate
`IsChamberCompatibleTransversal`. That predicate requires full
transversality, positivity of `F0`, and the additional equality

`(C0 S s * F0) ∩ D = C0Plus S s positiveRoots * F0`.

For every such choice, the positive product is a dominant valuation
section and its pairs `(c,f)` have distinct valuation values. The
statement does not assert that a chamber-compatible full transversal
exists or that compatibility follows from finite index or positivity.
The finite cover in the sixth conclusion need not be a transversal.

## Source and derived provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
V.2.3, printed105/PDF111, defines the positive character valuation and
its actual image; V.2.5, printed107/PDF113, gives the uniformizer
section; V.2.6, printed108/PDF114, gives the split-component
finite-index comparison; V.3.21–V.3.23, printed116–117/PDF122–123,
define the positive parts, choose positive finite representatives,
and form the dominant intersection. V.3.23 additionally makes the
chamber-compatible choice displayed above. V.5.1(4), printed122/PDF128,
prints both the representative union and the positive-product union
as disjoint.

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered
source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
§2.6(d), printed103/PDF134, and §5.2, printed187–188/PDF218–219,
are read with the 1 November 2024 *Corrections and additions*,
registered source `kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF24–25 and 30. The corrected character valuation has positive sign
and the corrected Cartan inequalities are nonnegative.

The packaging is derived. Uniformizer normalization compares the actual
maps. The two chamber-image descriptions are transported by the
published intrinsic image equivalence. Cutting full sections gives the
dominant sections. Positive transversals can be obtained by translating
each of finitely many representatives far enough along a strictly
positive uniformizer direction. The finite positive-cover target uses
the rational polyhedral chamber and the finite-index split-component
lattice; it requires only finitely many positive representatives and
does not infer a single positive representative per residue class.
Under the additional chamber equality, full product-pair uniqueness
restricts to the positive pairs. These are proof obligations; this
module contains no proof of the combined statement.

## Remaining geometric comparisons

The actual maximal compact `K0 = G(F)^1_x`, the KP parahoric `P_x`, and
their double-coset spaces do not occur in this unit. The corrected KP
indexing set is the dominant centralizer quotient by `Z(F)^0`. The
intended maximal-compact indexing set is the actual dominant valuation
image, equivalently the dominant quotient by the common norm kernel
`Z(F)^1`; establishing that equivalence relation for the shared `K0`
remains a separate actual-group statement. A full dominant valuation
section will index distinct `K0` double cosets only after that comparison.
A finite positive product cover will then supply a product covering,
with disjointness requiring the separate nonrepetition condition.
The same-`K0` standard-Levi comparison also remains outstanding.
