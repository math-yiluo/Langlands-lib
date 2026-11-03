# Extension from a represented dynamic centralizer

Author: Worker 1291.

This elementary interface works with any actual representative `j : L → G`
of `Dynamic.centralizer χ`, over any base scheme and in any universe `u`.
The generic construction requires the representing monomorphism and equality
of all-test ranges; it needs neither reductivity nor a chosen closedness proof.

For every subgroup functor `F` of `L`, `extendFromCentralizer χ j hj F` is
the exact product `j(F) U_G(χ)`. The image of `F` lies in `Z_G(χ)` and hence
in `P_G(χ)`. The already proved normalization of `U_G(χ)` by `P_G(χ)`
therefore supplies the hypothesis for `SubgroupFunctor.normalizedProduct`.
The membership theorem says, on each original test scheme `T`, precisely
that a point is `(l ≫ j) * n` with `l ∈ F(T)` and `n ∈ U_G(χ)(T)`.
The module also proves inclusion in `P_G(χ)` and monotonicity in `F`.
It does not assert parabolicity or representability of the resulting product.

Over an arbitrary field the membership condition specializes to
`rationalPointSubgroup`, which is evaluation at exactly
`Over.mk (𝟙 (Spec (CommRingCat.of k)))`. Thus the carrier agrees definitionally
with the identity-test carrier used by `dynamic_isSemidirectDecomposition`.
The final three lemmas evaluate the already published all-test
`range_inf_parabolic`, `range_inf_centralizer`, and `range_inf_unipotent`
at this same test. For a cocharacter `ν` of a closed subgroup `L`, they identify
the images of its dynamic parabolic, centralizer and unipotent subgroups with
the corresponding intersections in `G`. They impose closedness of `j`,
as do their imported all-test theorems.

These are algebraic carrier comparisons. The module defines no topology and
asserts no continuity or natural representation isomorphism. It uses the
existing represented-point equivalences through the imported
`Rational.ParabolicFunctor` interface.

The provenance is internal, by normalization, explicit factor membership,
and evaluation of existing all-test equalities. The structural correspondence
and dynamic realization of parabolics in this product remain separate
proposition targets. In particular none of those structural conclusions is
an input to this definition.
