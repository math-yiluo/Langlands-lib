# Scalar split component and form classes for Weil-restricted `GL_n`

`weilIso` identifies the Weil restriction of the base change of `GL_n` with the Weil restriction of `GL_n` over the upper field. Naturality of the Weil point comparison shows that the generic adelic equivalence followed by the matrix comparison is the exact point map of `IsWeilFormClass`.

The upper quotient uses the scalar torus, which is a split component in positive rank. The published character restriction theorems give injectivity and finite index for this torus. `map_positiveImage` identifies its positive subgroup with the image of the given lower positive subgroup.

`descends_iff` compares the two continuous descent conditions by composition with the quotient homeomorphism and its inverse. On upper adelic points, `continuousGeneralLinearEquiv` expresses the untwisted descent condition by evaluation in matrix coordinates. The homeomorphism therefore transports the exact representative identities. `isWeilFormClass_iff` adds the agreement of almost-everywhere classes using `coeFn_quotientL2Equiv` and `ae_quotient_iff`.

The matrix comparison uses the identification in Getz–Hahn, *An Introduction to Automorphic Representations*, §13.4, p. 350, `getz-hahn-2024-automorphic-representations`, SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The form-class comparison follows from that point identification and the two Library quotient constructions.
