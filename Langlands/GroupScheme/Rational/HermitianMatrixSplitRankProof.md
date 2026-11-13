# The attained Hermitian matrix split-rank comparison

`Langlands.GroupScheme.hermitianMatrixSplitRank.{u}` proves the exact published
proposition `Langlands.GroupScheme.HermitianMatrixSplitRankStatement.{u}`.
The universe `u` is arbitrary. All of the proposition's hypotheses are
retained: arbitrary fields with a separable quadratic extension, `n ≥ 2`,
an affine group scheme locally of finite type, an invertible Hermitian Gram
matrix, and an injective natural matrix presentation on every test scheme
whose image is exactly the determinant-one full Gram isometries.

Package the supplied matrix `J` and its Hermitian equation as the actual form
`H`. The adapter `Presentation.ofMatrixPoints` restricts each matrix map to
the prescribed special unitary subgroup and uses its injectivity and exact
image to obtain multiplicative equivalences, with the original naturality.

For the upper bound, `splitRank_le_wittIndex_of_matrixRepresentation` uses
injectivity, naturality and the full Gram preservation equation extracted
from the exact-image hypothesis. The finite-algebra matrix point comparison
turns the natural representation into a morphism to the unit group scheme
of the full matrix algebra, with a finite basis over the base field.
Pointwise injectivity makes this morphism a scheme monomorphism. Each actual
closed split subtorus remains a monomorphism after composition.

For such a torus the inverse universal matrix has Laurent coefficients.
Comparison with the inverse of the actual universal point transports its
full Gram preservation equation to that Laurent ring, with conjugation on
coefficients and fixed exponents. The matrix weight projectors supply an
extension-field basis of weight vectors; faithfulness makes their weights
generate the integral character lattice. A maximal family of nonzero weights
without opposite pairs has span rank at least the torus rank. The full Gram
equation makes the associated independent weight vectors pairwise
orthogonal, hence their span is an actual totally isotropic subspace of at
least that dimension. Its dimension is at most the attained Witt index.
Taking the supremum over all actual closed standard split subtori gives
`splitRank G ≤ H.wittIndex` in `ENat`.

For the lower bound, `Presentation.finrank_le_splitRank` starts from each
actual totally isotropic subspace. Nonsingularity of `J` gives nondegeneracy
of the full pairing. The hyperbolic decomposition construction extends the
subspace to that many hyperbolic planes with an orthogonal remaining block.
It uses the surjective trace map of a separable quadratic extension to adjust
the complementary vectors to be isotropic, so it also works in
characteristic two. Independent scaling on the hyperbolic pairs, with
inverse scaling on the partners and the identity on the remaining block,
defines a determinant-one isometry on every test scheme. The supplied
presentation transports these points to `G`. The resulting torus morphism is
closed: injectivity on all test points gives a monomorphism, and the
closed-subgroup theorem for torus monomorphisms into affine group schemes
locally of finite type gives the closed immersion.
Thus each subspace's dimension is at most the actual `splitRank G`.
Applying this result to a subspace attaining `H.wittIndex` gives the reverse
inequality.

The two bounds identify the finite attained Witt index with `splitRank G`.
The pairing interface supplies a subspace attaining that index. Finally,
`linearFirst_eq_dotProduct` identifies its full pairing with the target's
`bar(b)` dotted with `J.mulVec a`; the proof explicitly converts between
pairwise isotropy of submodule elements and the form's membership-based
predicate. This gives both the attained equality and the bound for every
actual totally isotropic submodule.

The proof is an internal comparison of actual closed split tori and actual
subspaces using the imported matrix, Laurent weight and hyperbolic
constructions. Its route supplies the scheme-level comparison required by
the published target. It uses no outer-form classification, rank-one
identification, or Kneser–Tits result. No assumption on characteristic or
field cardinality is added, and pairwise total isotropy is retained
throughout.
