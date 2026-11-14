# Congruence for all geometric characters of Weil restriction

This derived helper concerns the actual Weil restriction of the multiplicative
group for a finite field extension `E/k`. It assumes tensor evaluation is
bijective over the coefficient field `Ω` and that every `k`-embedding of `E`
into `Ω` preserves the specified real additive valuations. The splitting
condition is supplied by the published finite-separable embedding theorem
when the coefficient field splits the relevant minimal polynomials.

`weilGm_rationalExtend_mem_characterCongruence` carries membership in the
unit congruence subgroup of `E` to the character congruence subgroup of the
actual base-changed Weil restriction. The proof applies the rational
embedding-character monomial formula: each embedded unit belongs to the
same-depth congruence subgroup by valuation preservation, and the subgroup
is closed under integer powers and finite products.

`weilGm_rationalExtend_mem_characterCongruence_of_pos` only requires a bound
on the difference from one at positive depth. The published unit-filtration
lemma then supplies valuation zero. Finally,
`weilGm_rationalCharacterEval_sub_one_le_of_pos` expresses the resulting
bound directly for every geometric character and a prescribed unit coordinate.

`weilGm_unitCongruenceHom` packages the subgroup membership proof as a
multiplicative map from the depth-`r` unit filtration in `Eˣ` to the
depth-`r` character congruence subgroup. Its underlying point is
`WeilGm.extendedUnitPoint` of the input unit. Its multiplication and identity
laws are those of that point-extension homomorphism, and
`weilGm_unitCongruenceHom_coe` records the underlying point explicitly.

These are internal consequences of existing constructions and do not add
an external literature claim.
