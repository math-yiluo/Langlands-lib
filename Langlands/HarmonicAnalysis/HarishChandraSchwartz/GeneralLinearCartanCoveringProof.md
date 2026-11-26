# Cartan coverings on actual general linear points

`generalLinearCartanCovering` proves both clauses of
`GeneralLinearCartanCoveringStatement` for every nonarchimedean local
field \(F\) and every rank \(N\). The argument is uniform in \(N\); the
ranks zero and one need no separate case. It combines three published
inputs: the matrix Cartan decomposition
`Langlands.GeneralLinear.Cartan.cartanDecomposition`, the standard-model
comparison `mem_standardIntegralModel_integralPoints_iff`, and the
standard-parabolic description `generalLinearStandardParabolic`.

## The uniformizer and the canonical lattice section

Every matrix factorization uses the uniformizer
`SplitTorusValuation.uniformizerUnit F`, written \(\varpi\). This is
the element that the canonical section
`CocharacterUniformizer.latticeSection` evaluates cocharacters at. The
value-group identification
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` with
\(\mathbb Z^{\times}_0\) together with `LocalField.ord_uniformizer`
gives \(\varpi\) normalized value \(\exp(-1)\). Hence \(\varpi\) has
value below one and its integer powers realize every nonzero value,
that is, \(\varpi\) is an `Iwasawa.IsUniformizingElement`, as the
matrix Cartan decomposition requires.

For integer weights \(w\), the torus point used in the proof is the
canonical section at the cocharacter `cocharacterOfWeights F w`. Its
image in \(\mathrm{GL}_N(F)\) under `rationalPointsEquiv` is the
diagonal matrix `Iwasawa.torus ϖ w` \(=\operatorname{diag}(\varpi^{w_i})\).
This follows from `cocharacterOfWeights_comp_diagonalTorus` and the
affine-point formula `pointsEquiv_diagonalCocharacter` for the diagonal
cocharacter. So the diagonal factor of the matrix decomposition is the
image of the canonical section at a cocharacter, and this point lies in
\(C_A\).

## Root inequalities

`characterNorm_latticeSection` gives the norm of a character
\(\alpha\) at the section point as \(q^{-\langle\alpha,w\rangle}\), where
\(q\) is the residue cardinality. Since \(q>1\), this norm is at most one
whenever \(\langle\alpha,w\rangle\ge 0\). By
`simpleRelativeRoots_diagonalTorus`, the strictly decreasing reference
cocharacter has the adjacent characters `simpleRootCharacter` as its
simple roots. By `latticePairing_simpleRootCharacter` and
`cocharacterCoordEquiv_cocharacterOfWeights`, the \(j\)-th of these pairs
with \(w\) as \(w_j-w_{j+1}\).

In the ambient case the Cartan exponents are antitone, so every such
difference is nonnegative and the section point lies in \(C_A^+\) of
all simple roots. For a standard Levi only the roots of \(J\) are
required. These are the uncut edges of the block shape, and the two
coordinates of an uncut edge lie in one block
(`blockIndex_adjacent_eq_iff`). They are ordered there by
`Langlands.Geometric.index_strictMono`, so the antitonicity of that
block's exponents gives the inequality.

## Transport of the integral factors

By `mem_standardIntegralModel_integralPoints_iff`, a rational point lies
in the integral points \(K_0\) of the standard model exactly when its
matrix lies in `Iwasawa.integralRange`, the image of
\(\mathrm{GL}_N(\mathcal O_F)\). In the ambient case the two integral
matrix factors are carried back along the inverse of
`rationalPointsEquiv`, and they lie in \(K_0\) by this comparison.
Injectivity of `rationalPointsEquiv` then turns the matrix identity
\(g=k_1\operatorname{diag}(\varpi^{w})k_2\) into the identity
\(g=k_1\cdot 1\cdot a\cdot k_2\) of rational points.

For \(M_J(F)\) the strict antitonicity of the reference cocharacter makes
it generic (`isGenericCocharacter_diagonalTorus_iff`). Then
`generalLinearStandardParabolic` gives a unique consecutive block shape
\(B\) whose uncut edges are \(J\), and identifies the actual rational
points of the Levi with the block-diagonal subgroup `B.leviSubgroup`.
The matrix Cartan decomposition is applied in each block. The integral
block factors assemble under `B.leviEmbedding` to a matrix over
\(\mathcal O_F\), so their transport lies in \(K_0\cap M_J(F)\). The
block-diagonal matrix of the blockwise powers of \(\varpi\) is the
diagonal matrix of the assembled weights. Applying the block embedding
to the blockwise products gives the decomposition of the rational point.

In both coverings the set of centralizer factors is the singleton
\(\{1\}\).

The source correspondence is Renard V.3.23 and V.5.1(4)–(5),
and Waldspurger I.1(4) and the Levi Cartan decomposition used in
II.4.5, with exact editions and locators in
[the statement](GeneralLinearCartanCoveringStatement.md).
