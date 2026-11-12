# Normalized root-Levi height bounds from preceding-intersection minima

This derived unit supplies a higher-rank use of the explicit universal arithmetic
rank-one height premise. It transfers one simultaneous prefix minimum to the full
rational group of a singleton standard Levi, constructs its intrinsic norm-one
normalization, and bounds the normalized point's selected-vector height. The
arithmetic premise remains explicit. Neither a bound for all chamber roots nor
the general chamber-reduction theorem is concluded here.

`HasBoundedStandardLeviNormalization` records actual normalization data for a raw
adelic point of a canonical standard Levi. These consist of a split component,
its factor through the original torus, a point of its intrinsic positive torus,
and an intrinsically norm-one Levi point. The ordered product is the original
raw point. The normalized point retains the full rational approximate-minimum
inequality with constant `c` and has height at most `c C`. Norm-one membership
of the original raw point is not required.

The rational inclusion lemma assumes that an index set `J` is contained in each
of the preceding individual parabolic index sets. Monotonicity of actual standard
Levis, followed by inclusion of each Levi in its parabolic, puts every rational
point of `L_J` in the preceding rational intersection. This does not require the
individual parabolic index sets to be nested.

For one index `l` in a finite chain of minima, factor the ambient point as the
canonical Levi image of a raw point times its canonical unipotent image. The
selected representation preserves its line on the `l`th individual parabolic.
Every valid standard unipotent lies in this parabolic, and unipotence changes
line preservation to vector fixedness. Every tested rational Levi point
normalizes the canonical unipotent. Consequently that right factor is removable
both before and after the rational translation, and the prefix minimum becomes
the full rational approximate-minimum inequality in the raw Levi. This checks
the normalization required for transporting minima.

For a simple root `alpha` absent from the `l`th parabolic index, its singleton
Levi has exactly `{alpha}` as simple relative roots. Its lifted original torus
is maximal split and the original generic cocharacter remains generic. The
published actual standard-family intersection theorem makes the restriction of
the exact ambient parabolic line have precisely the empty-index standard
parabolic as stabilizer in this Levi. The universal arithmetic premise therefore
applies to this actual restricted representation, without replacing it by an
unrelated matrix representation.

The final theorem assumes `alpha` belongs to every preceding parabolic index.
The raw restriction lemma gives the full rational minimum on its root Levi.
The published split-component construction supplies a central split component
whose inclusion factors through the original torus, hence preserves the selected
line. Its positive factor scales both sides of every height comparison by the
same positive character norm. The published central normalization theorem
therefore constructs an intrinsic norm-one point with the same minimum constant.
The arithmetic bound controls this point's height by `c C` for every `c >= 0`.
The positive `C` is chosen before `c` and all adelic points.

In the usual enumeration of distinct simple roots, taking each individual
parabolic index to be the simple-root set with its own root removed supplies
these inclusion conditions. This module does not construct such an enumeration
or assert its simultaneous chamber conclusion. All provenance is internal and
derived from published actual standard-family comparisons, primitive-vector
height identities, preceding-intersection minima and central positive
normalization. No external source theorem is quoted.
