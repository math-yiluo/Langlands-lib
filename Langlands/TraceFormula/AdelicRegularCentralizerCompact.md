# Compact rational quotients of regular elliptic adelic matrix centralizers

`adelicRegularCentralizerCompactQuotient` applies to a rational matrix over a number field
whose characteristic polynomial is irreducible and separable. It proves compactness of the
left quotient of the centralizer in the determinant-norm-one adelic matrix group by its
intersection with the rational matrix group.

For a rational matrix `g` with characteristic polynomial `p`, the proof uses the field
`AdjoinRoot p`. Evaluation on a rational cyclic vector identifies multiplication by its
distinguished root with `g`, in the basis obtained by pulling back the standard vector
basis. The regular representation extends to the full adeles using
`numberFieldAdeleTensorEquiv` and the scalar extension of that basis. Its matrix entries
are the continuous coefficients from `adeleBasisEquiv`, applied to products with principal
basis elements. Continuity on units follows for the existing units topology.

The rational cyclic basis extends to the adele ring. The lemma `exists_sum_pow_of_commute`
then expresses any commuting matrix as a linear combination of powers of the image of `g`.
Each such matrix is in the image of the regular representation. Injectivity and the same
argument on inverse matrices give preimages for commuting matrix units. The determinant
is the tensor norm by `Algebra.norm_eq_matrix_det`. The lemmas
`numberFieldAdeleTensorNormUnits_eq` and `AdelicFunctoriality.full_ideleNorm` identify its
normalized absolute value with the upper-field idelic absolute value. Thus the norm-one
idele group maps continuously onto the determinant-norm-one centralizer. Principal
ideles map to rational matrices by compatibility of the regular representation with
scalar extension. The compact fundamental set of `NormOneIdeleClass.exists_isCompact_fundamentalSet`
maps onto the rational left quotient, which proves compactness.

For the compatible regular measures, compactness gives finiteness of the centralizer volume for
these rational `GL_n` classes. Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
gives the volume convention in equation (18.14), printed p. 479. In §18.4, printed p. 485,
ellipticity means finiteness of the ordinary centralizer volume, and equation (18.27) uses
`τ(C_γ)` as the volume factor. Section 2.6, equations (2.19)–(2.22) on pp. 68–69, gives the
norm-one convention and its relation to the positive scalar quotient. The retained source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
