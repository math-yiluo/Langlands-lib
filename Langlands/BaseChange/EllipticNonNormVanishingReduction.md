# Off-norm vanishing on the elliptic set

`EllipticNonNormVanishingReductionStatement.{u,v}` is the off-norm branch of the
unramified spherical fundamental lemma restricted to regular elliptic elements.
It assumes `EllipticNormCriterionStatement.{u,v}` and the Satake character
statements over the base and extension field universes. Given a cyclic unramified
extension \(E/F\) of degree \(l\), an unramified base-change homomorphism \(b\)
and a spherical Hecke function \(\phi\), the ordinary orbital integral of
\(b(\phi)\) at a regular elliptic non-norm \(\gamma\) vanishes for every measure
on the centralizer quotient.

The proof first identifies the norm condition on a regular elliptic element with
membership of its determinant in the scalar norm subgroup, by the elliptic norm
criterion. This subgroup is the image of Mathlib's algebra norm on units. The
Library's `LocalClassField.unramifiedNormMembership` identifies membership with
divisibility of the determinant order by the extension degree. The
`isNorm_elliptic_iff_dvd_det` equivalence composes these two equivalences using
the degree in the cyclicity hypothesis.

For a regular elliptic non-norm the resulting determinant order is outside
\(l\mathbb Z\). The Library's determinant-support reduction then gives zero
orbital integral under Satake separation over \(F\) and Satake character
existence over \(E\). It applies to the same orbital integral and the same
quotient measure as `VanishesOffNorms`.

This is a derived internal reduction for the proof of the fundamental lemma
`FundamentalLemmaStatement`. The determinant-support
argument appears in the remark after Henniart–Lemaire I.6.11 (printed p. 53,
PDF p. 61), and the regular elliptic norm criterion is the lemma of I.6.12 on
the same page. Arthur–Clozel, Chapter 1, Lemma 1.4 (printed pp. 8–9,
PDF pp. 22–23), gives the elliptic criterion for cyclic field extensions.
