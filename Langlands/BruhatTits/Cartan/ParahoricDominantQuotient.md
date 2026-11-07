# The actual dominant quotient for a parahoric

This internal construction specializes `RestrictedRightQuotient` to the actual
objects in `ParahoricBuildingData G`. It constructs the quotient and its canonical
double-coset map. It does not assert a Cartan decomposition.

Here `F` is a nonarchimedean local field of mixed or equal characteristic, `G` is
an affine group scheme over `F`, and `B : ParahoricBuildingData G`. The data contain
the connected reductive group, the maximal split inclusion `B.i : S → G`, its
represented algebraic centralizer `B.centralizer.j : Z → G`, and the factor
`B.centralizer.s : S → Z`. The factorization and character comparison are fields
of these actual data; no arbitrary subgroup is substituted for the centralizer.
No existence of such data is asserted.

The motivating source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), §5.2, (5.2.1)–(5.2.2) and Theorem 5.2.1, printed pp.187–188, PDF
pp.218–219, together with the authors' corrections of 1 November 2024, PDF
pp.24–25 and 30. Source identifiers are
`kaletha-prasad-2023-bruhat-tits-new-approach` and
`kaletha-prasad-2024-corrections`.

## Normalization and indexing set

`parahoricDominantSet B ν` is the existing `dominantCentralizer` for the actual
factor `B.centralizer.s` and the positive relative roots selected by the
cocharacter `ν`. Its defining inequalities are

`0 ≤ eval S a (centralizerValuation s h z).toAdd` for every positive relative root.

The valuation is positive: its pairing with a restricted rational character is
`ord_F(χ(z))`. The correction reverses the printed inequality in (5.2.2), so these
inequalities agree with both corrected formulas. Apartment translation uses the
negative valuation and is not the map used for dominance. The construction does
not require `ν` to be generic; the actual Cartan statement will require it.

`ParahoricDominantQuotient B ν` is the set quotient of this dominant set by

`z ∼ z'` if and only if `z' * z⁻¹ ∈ B.centralizerZero`.

The relation is the restriction of a right-coset setoid. It therefore needs
neither normality of `Z(F)^0` nor a proof that the dominant set is invariant under
it. The class constructor is `parahoricDominantClass`; its equality criterion is
`parahoricDominantClass_eq_iff`.

`B.centralizerZero` is the actual `Z(F)^0` defined from the unramified norm data of
KP Definition 2.6.23. It is distinct from `rationalCommonNormKernel Z = Z(F)^1`.
Likewise `P = B.parahoricAt x` is the actual Chapter 7 parahoric, not the norm-one
stabilizer `K₀ = G(F)^1_x` or the full fixer.

## Well-definedness and the conditional equivalence

`parahoricDominantRespects` proves the precise well-definedness condition:
`z' * z⁻¹ ∈ Z(F)^0` implies equality of the `P_x` double cosets of `j(z)` and
`j(z')`. The implemented proof uses the existing inclusion
`B.map_centralizerZero_le_parahoric {x}` and the identity
`j(z') = j(z' * z⁻¹) * j(z) * 1`. This is an intrinsic law of the construction;
it uses no Cartan theorem, validity certificate, or special-vertex premise.

`parahoricDominantDoubleCosetMap` is consequently a well-defined function from
the displayed set quotient to `P_x \ G(F) / P_x`, with the proved class formula.
It is not declared injective or surjective.
`parahoricDominantDoubleCosetEquiv` packages this same function as an equivalence
only when its bijectivity is supplied explicitly, and its class formula is proved.

The actual coverage, converse equality criterion and bijectivity are separate
statement and proof obligations. For the maximal compact subgroup the intended
indexing set instead uses the relation induced by `K₀` double cosets, compared
separately to `Z(F)^1` and the chamber in the actual valuation image. There is no
universal dominant-cocharacter indexing in this construction.
