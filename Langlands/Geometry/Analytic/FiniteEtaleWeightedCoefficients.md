# Weighted coefficients and finite étale affinoid fibres

Let `f : A → B` be a bounded map of presented affinoid algebras over a
complete ultrametric normed field. Assume `f.IsFiniteBanach` and
`f.AlgebraicallyFiniteEtale`. For a family \(b_0,\ldots,b_n\) generating
the unit ideal of \(B\) and positive real weights \(w_0,\ldots,w_n\),
`BanachSpectrum.exists_weightedCoeff_iff` constructs a polynomial
\(P\in A[X_0,\ldots,X_n]\) whose coefficients generate the unit ideal of
\(A\). A point \(x\) of \(\mathcal M(A)\) has a lift \(y\) to
\(\mathcal M(B)\) with \(y(b_j)w_j\le y(b_0)w_0\) for all \(j\) if and
only if some exponent \(d\) with \(d_0>0\) maximizes
\(x(P_d)\prod_j w_j^{d_j}\).

The finite étale algebra \(B\) is finite projective over \(A\), so
`exists_normPolynomial` supplies \(P\). If all its coefficients lay
in a maximal ideal of \(A\), the polynomial would vanish after base
change to an algebraic closure of the residue field. The finite étale
algebra splits there as a product of copies of the field
(`Algebra.FormallyEtale.equivPiOfIsSepClosed`). The norm polynomial
specializes to a product of linear forms, one per coordinate. Each form
is nonzero because the \(b_j\) generate the unit ideal in \(B\). The
product is nonzero, including when it is empty, so the coefficients
generate the unit ideal in \(A\).

Over an algebraically closed ultrametric normed extension, every
homomorphism from the split fibre to that field is evaluation at a
coordinate. The proof uses the coordinate idempotents, whose sum is
one. The coefficient criterion then follows from
`exists_maximalWeightedCoeff_pos_iff` applied to the product of the
coordinate linear forms.

To apply the criterion to a point, the proof embeds a completed residue
field isometrically in an algebraically closed ultrametric normed field.
`FiniteRadiusRealization` first produces a complete extension with an
element of norm two. The spectral norm on its algebraic closure preserves
the norm. This construction applies also to trivially normed residue
fields.

Given \(y\) over \(x\), use the field obtained from the completed residue
field at \(y\). The residue map from \(B\) has the norms prescribed by
\(y\), and its composite with \(f\) has those prescribed by \(x\). The
criterion gives the required exponent. Conversely, use the field
obtained from the completed residue field at \(x\) and apply the
criterion to find an \(A\)-algebra homomorphism from \(B\) satisfying
the inequalities. Its composite with \(f\) is contractive, since \(x\)
is a Banach spectrum point. The finite Banach coefficient estimate
`BoundedAlgHom.IsFiniteBanach.exists_norm_bound` makes the homomorphism
bounded on \(B\), so its norm defines the required point \(y\).
