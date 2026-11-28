# Canonical square-integrable classes of cusp forms on `GL_n`

`Langlands.Automorphic.DiscreteHeckeIsolation.GeneralLinearCanonicalCuspidalFormClassStatement`
quantifies over a number field `F : Type` with compact additive adele quotient and a cuspidal
operator realization `S` of `GL_{r+1}`. If the forms of `S` are invariant under the positive split
centre, then each form has a class for the canonical measure on `[GL_{r+1}]`.
`IsCanonicalGeneralLinearFormClass` matches the class with the continuous function descended from
the form by the canonical identification of the two split-centre quotient models.

The proposition is the first conclusion of `GeneralLinearDiscreteCuspidalHeckeIsolationStatement`
with its own hypotheses. The square-integrability argument is the inclusion of split-centre-invariant
cusp forms in `L²_cusp([G])` at the start of the proof of Getz–Hahn, Theorem 9.7.3. The split-centre
convention is the positive real component in (2.20), or the positive scalar matrices in the
matrix model of `GL_{r+1}`. Compactness of the additive adele quotient is the instance used by
`CuspidalOperatorRealization`.

J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, Springer, 2024,
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`, (2.20), p. 68 (PDF p. 85),
and Theorems 9.7.1 and 9.7.3, pp. 264–265 (PDF pp. 276–277).
