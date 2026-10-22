# Actual archimedean matrix and Hilbert growth comparison

The theorem `Langlands.Global.archimedeanHilbertGrowthComparison` proves the
published proposition
`Langlands.Global.ArchimedeanHilbertGrowthComparisonStatement K n`.
Its parameters are exactly `(K : Type u) [Field K] [NumberField K] (n : ℕ)`.
The universe is arbitrary, and the rank may be zero. The target and its
imported constructions are unchanged. The proof adds no comparison assumption,
regularity assumption, or positive-rank hypothesis.

This is an internal, derived finite-coordinate argument for the concrete
norms in the imported statement. Its source context is documented in
[the statement pair](ArchimedeanHilbertGrowthComparisonStatement.md): the
Hilbert norm convention and finite-slice growth condition come from
Borel–Jacquet, while the particular linear estimates below are derived here.
No independent assertion about compact maximality is used or proved.

## Uniform linear comparison

Write `H(g)` for `ArchimedeanGL.matrixHeight K n g`, `h(g)` for
`infiniteAdelicHilbertNorm K n g`, and `S(g)` for
`infiniteAdelicLocalEntrySq K n g`. The imported squared-norm identity is

\[
 h(g)^2=1+S(g)+S(g^{-1}).
\]

Let `r` and `s` be the cardinalities of the real and complex infinite places,
respectively, and put `m=(r+s)n²`, regarded as a nonnegative real number.
The theorem `archimedeanMatrixHilbertComparison` uses the explicit constants

\[
 C=n+1>0,\qquad D=\sqrt{1+2m}>0.
\]

The private helpers `sum3_nonneg` and `term_le_sum3` apply
`Finset.sum_nonneg` and `Finset.single_le_sum` to the three nested finite
sums over place, row, and column. They show that each local squared entry
is at most `S(g)`, and hence at most `h(g)²`. Nonnegativity then bounds each
real or complex entry norm by `h(g)`. The product norm and finite-function
norm lemmas `norm_prod_le_iff` and `pi_norm_le_iff_of_nonneg` give the same
bound for each mixed entry. Thus the supremum over places is taken inside
each row sum, exactly as in the published matrix norm.

The helper `rowNorm_le_card_mul` uses
`Matrix.linfty_opNNNorm_def`, `Finset.sup_le`, and a termwise sum bound to
show that a matrix whose entries have norm at most `a ≥ 0` has row norm at
most `n*a`. Applied to the forward matrix and the actual inverse, it gives
both row norms at most `n*h(g)`; the inverse case reuses
`infiniteAdelicHilbertNorm_inv`. Finally, `1 ≤ h(g)` bounds the scalar part
of the height, yielding `H(g) ≤ (n+1)*h(g)`.

For the reverse direction, `norm_entry_le_rowNorm` uses the same row-norm
formula: a single nonnegative entry norm is at most its row sum, which is
at most the row supremum. The lemmas `norm_le_pi_norm`, `norm_fst_le`, and
`norm_snd_le` then bound every local entry by `H(g)`. Squaring and summing
termwise yields `S(g) ≤ m*H(g)²`. Applying the same estimate to the inverse
and using `matrixHeight_inv` yields `S(g⁻¹) ≤ m*H(g)²`. Since `H(g) ≥ 1`,

\[
 h(g)^2\le (1+2m)H(g)^2=(D H(g))^2.
\]

The proof uses `Real.sq_sqrt` and `sq_le_sq₀` with nonnegative sides to
conclude `h(g) ≤ D*H(g)`. Both comparison constants are chosen before `g`.
The scalar and inverse blocks remain in the squared-norm identity, and
complex places are counted once, with no extra multiplicity.

All finite sums and suprema allow empty indexing types. At `n=0`, the
matrix row norms and local sums vanish, `m=0`, and both selected constants
are one. The scalar block makes `h(g)=1`, while the scalar maximum makes
`H(g)=1`. The uniform proof therefore includes this case without a split.

## Growth equivalences and aggregate

`archimedeanHilbertGrowthEquivalence` obtains the two positive constants
from the comparison theorem. A matrix-growth bound `B*H(g)^d` becomes
`(B*C^d)*h(g)^d`, and a Hilbert-growth bound `B*h(g)^d` becomes
`(B*D^d)*H(g)^d`. The proof uses `pow_le_pow_left₀`, multiplication by the
nonnegative bound, and `mul_pow`. The new bound is nonnegative, and the
natural exponent is unchanged. Zero bounds and zero exponents are
included. The argument applies to every complex-valued function on the
actual infinite adelic group; it requires no continuity or smoothness.

`adelicHilbertGrowthEquivalence` applies that function-level equivalence
to `Langlands.Automorphic.infiniteSlice K n b f` for each finite adelic
slice `b`, using `forall_congr'`. Both the bound and exponent are still
chosen after `b`; no uniformity over finite slices is introduced.

The final theorem assembles these three results in the exact conjunction
order of the published aggregate proposition.
