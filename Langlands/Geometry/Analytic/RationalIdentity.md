# Rational localizations already represented by the base algebra

Authors: Worker 36 (Lean proof and original Markdown) and Worker 227
(Markdown audit against the implementation).

The closing theorem `Langlands.Analytic.RationalIdentity.identity` proves
`Langlands.Analytic.RationalIdentity.IdentityStatement` from the separate
statement module. The fractions themselves are defined in
`RationalIdentity/Definitions`. The rational quotient
`RationalLocalization.algebra`, its base map, the bounded lift
`liftFromBase`, the uniqueness theorem `hom_ext_base` and the exact image
formula `range_comap_baseMap` are imported from the published
`RationalLocalization` module.

The input is an actual unit of a presented strict affinoid algebra, a finite
numerator tuple, and a proved bound on the monomials of the actual fractions
formed using that unit's inverse. The theorem `generatesUnitIdeal` shows
that the denominator being a unit directly implies the required unit ideal,
since `g⁻¹ * g = 1` lies in the span. This also holds for the zero algebra.
The theorem `fraction_equation` records `g * (g⁻¹ * f_i) = f_i`.

The definition `retraction` applies `liftFromBase` to the identity of `P`
and these fractions. This is convergent Tate evaluation at the fractions,
and it gives a bounded map from the actual rational quotient back to the
original algebra. By `retraction_comp_baseMap`, its composite with the base
map is the identity. In `baseMap_comp_retraction`, uniqueness of bounded
maps out of a rational quotient over the base (`hom_ext_base`, with the
unit ideal above) shows that the opposite composite is also the identity.
`BoundedAlgEquiv.ofHomInv` turns these two maps into the bounded algebra
equivalence `equiv`. Its forward map is the base map by definition
(`equiv_apply`), and its spectrum homeomorphism is definitionally the
pullback along the base map (`spectrumHomeomorph_apply`). The exact image
formula identifies the range of this pullback with the rational locus.
Because the homeomorphism is surjective, `locus_eq_univ` shows that the
locus is the whole spectrum.

For unit-ball numerators, `bounded_of_norm_le_one` uses the power
criterion `hasBoundedMonomials_iff_pow_bound`. Induction bounds every
power by the maximum of one and the norm of one. The necessary bound is
therefore proved without a norm-one instance, which the zero quotient
lacks. With denominator one, the fractions simplify to the numerators.
`unitRadiusEquiv` therefore shows that adjoining equations `Y_i = f_i` for
such numerators preserves the bounded algebra. `emptyEquiv` specializes to
the empty tuple, whose norm hypothesis holds vacuously. This gives an
unconditional identity chart, also when the algebra is zero. In both
specializations the forward map is the base map by `rfl`.

The proof makes no case split on the number of numerators, on whether `P`
or the quotient is zero or nonreduced, or on whether the valuation of `K`
is trivial. Completeness of `K` is used only through the imported
rational-quotient constructions. The statement is universe polymorphic in
`u`. Inspection of the closing theorem reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

This is an internal consequence of the constructed bounded-tuple
localization property, in the setting of Berkovich's Trieste 2009 lectures,
Definition 2.2.1 and Exercise 2.2.2(ii), page 9. The fraction bound is an
explicit hypothesis about elements of the original algebra. No general
spectral inequality-to-power-bound implication, inverse from spectral
nonvanishing, analytic-domain output or structure sheaf is assumed or
proved.

Registered original: `berkovich-2009-trieste-analytic-spaces`, content SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Original URL: https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.
