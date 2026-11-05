# Norm images in a tower of splitting fields

Let `k → L → M` be a compatible tower of fields at arbitrary universe `u`,
with all three extensions finite Galois. Let `vL` and `vM` be valuations
with possibly different ordered value groups, such that `vM` extends `vL`
and is invariant under `Gal(M/L)`. Assume that every valuation-one unit of
`L` is the norm of a valuation-one unit of `M`. Let `T` be an affine
commutative group scheme over `k` whose base change to `L` is a split torus.

`torusNormIwahori_eq_of_tower` proves equality of the two actual bounded
norm images in `T(k)`. The character-valuation kernels and rational norm
maps are those of `KPZeroSubgroups`; the theorem does not replace their
carriers or assume an equality of images. `torusNormTowerEquiv` is the
multiplicative equivalence induced by this subgroup equality, and its
underlying map is the identity on ambient rational points.

The forward inclusion applies `relativeBoundedRationalNorm` to an upper
bounded lift and uses `rationalNorm_relativeRationalNorm`. The reverse
inclusion lifts a lower bounded point through
`relativeBoundedRationalNorm_surjective_of_split` and uses the same norm
tower law. Splitness and the scalar norm assumption are therefore used to
construct the required lift.

This is internal infrastructure for the nested-splitting-field step in
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Lemma 2.5.12,
printed pp.89–90 (PDF pp.120–121). Its proof follows that step through the
previously constructed relative norm. The local-field scalar norm theorem,
comparison of arbitrary splitting fields through their compositum, and
independence of the final zero subgroup are separate results; this module
asserts the stated tower comparison under its explicit scalar hypothesis.
