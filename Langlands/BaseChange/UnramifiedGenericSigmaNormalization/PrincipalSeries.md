# The canonical action on unramified principal series

For the actual normalized principal series `principalSeriesOfTuple E z`,
`principalIntertwiner` is pullback by the inverse entrywise field automorphism,
with the identity on the inducing coefficients. This convention gives
`A (I(g) f) = I(g^σ) (A f)` for the right-translation action. The canonical
pullback is the operator of Henniart–Lemaire I.5.4, printed p. 33 (PDF p. 41),
with the inverse convention for precomposition. See the source details in the
[normalized σ-action statement](../UnramifiedGenericSigmaNormalizationStatement.md).

The canonical normalized order is invariant under the field automorphism. This
preserves each rank-one inducing character and each determinant norm in the
parabolic half modulus. The tensor-product action is unchanged because its
values on pure tensors agree. `borelInducing_sigma` records the resulting
invariance of the full inducing action. `Induction.transportSmoothEquiv`
then gives the σ-intertwining equivalence and `eval_principalIntertwiner`
records its formula on sections.

For a spherical section, right invariance makes its value at each element of
the spherical subgroup equal to its value at the identity. The Iwasawa
factorization and Borel covariance therefore determine the section from that
value. The inverse automorphism preserves the spherical subgroup and the
Borel action, so `principalIntertwiner_spherical` fixes the section pointwise.
This is the spherical identity used in the proof of Henniart–Lemaire I.5.5,
Lemma 2, printed p. 39 (PDF p. 47).

`principalSeries_whittakerType` applies the normalized-product preservation of
Whittaker type to the rank-one inducing representations. In particular, the
functional space for every standard nontrivial additive character is a complex
line. The proof uses `RankinSelberg.normalizedProductWhittakerType` with the
scalar rank-one input `RankinSelberg.scalar_isOfWhittakerType_rankOne`.
