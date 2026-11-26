# Adelic radical integral vanishing for `GL_n`

`Langlands.TraceFormula.generalLinearRadicalIntegralVanishing` proves
`Langlands.TraceFormula.GeneralLinearRadicalIntegralVanishingStatement.{u}`.

Fix a proper rational parabolic. The theorem
`exists_properRationalParabolicRadicals_eq_comap` expresses its radical as the inverse image of
a weight-block radical under rational conjugation and supplies indices with `e i < e j`.
The threshold at `e i` gives a two-level weight, and `blockUnipotent_le_of_le` places its
radical inside the original weight-block radical. The indices `j` and `i` witness the
positivity of the two block sizes after the permutation supplied by
`exists_perm_thresholdWeight_eq_twoBlockWeight`.

The insertion of the standard two-block matrices at `v` is a continuous homomorphism from
the additive matrix group. Projection onto the finite factor, evaluation at `v`, and
extraction of the upper block give a continuous left inverse, so the insertion is a closed
embedding. The matrix entry conditions hold at `v` by `blockUnipotent_mem` and at every
other component because the inserted matrix is the identity there. The adelic point
comparison and the inverse permutation and rational conjugations carry this closed
image into the radical of the given parabolic.

The translated test function remains continuous with compact support on the closed adelic
radical. Compactness of the radical's rational quotient gives right invariance of its Haar
measure via `haar_isMulRightInvariant_of_compactRationalQuotient`. Haar measure on the
one-place subgroup is right invariant by commutativity and transports to additive Haar
measure on the matrix coordinates. In each left coset, the conjugating factors and the
coset representative are absorbed into the two translations in the local vanishing
hypothesis. The subgroup average is therefore zero on every coset.
`compatibleMeasureExists` and its Weil integral formula give zero for the integral over
the full adelic radical. Scaling Haar to `properParabolicHaarMeasure` preserves this equality.

This is the vanishing step in the proof of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Definition 16.4.1 and Lemma 16.4.2, printed p. 430 (PDF p. 438).
The registered source `getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
[Getz–Hahn, *An Introduction to Automorphic Representations*](https://doi.org/10.1007/978-3-031-41153-3)
