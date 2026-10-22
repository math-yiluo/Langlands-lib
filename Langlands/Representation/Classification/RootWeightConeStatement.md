# Root and weight cones for the exhaustion argument

`Langlands.RootWeightConeDecompositionStatement` is a proposition definition,
not a theorem proof. It states the finite Euclidean lemma used in Silberger's
exhaustion argument. Worker 19 authored this pair.

Let \(\{\alpha_i\}_{i\in I}\) and \(\{\lambda_i\}_{i\in I}\) be bases of a real
inner product space, with \(I\) finite, such that
\((\alpha_i,\lambda_j)=\delta_{ij}\) and
\((\alpha_i,\alpha_j)\leq 0\) for \(i\ne j\).
For every vector \(x\) there is a unique subset \(F\subseteq I\) for which
\[
x=\sum_{i\in F}c_i\lambda_i-\sum_{i\notin F}d_i\alpha_i,
\qquad c_i>0,\quad d_i\geq0.
\]
Only \(F\) is bound by the uniqueness quantifier. The coefficient functions
existentially quantify values on all of \(I\); unused values are unrestricted.
In particular, the statement does not falsely assert uniqueness of those unused
values. Empty index sets and the zero-dimensional space are included.

The Lean declaration quantifies the index type and vector-space type in
independent universes. `Module.Basis` supplies actual linear independence and spanning;
the inner product and its positivity come from Mathlib's
`InnerProductSpace ℝ E`. Duality and the off-diagonal inequalities are explicit
hypotheses. No classification, cone decomposition, chamber choice, or
canonical representative is supplied as a field of an object. The conclusion
is an actual vector equality between finite sums, with strict positivity on
the weight side and weak positivity on the root side.

The original source is A. J. Silberger, *The Langlands quotient theorem for
p-adic groups*, Mathematische Annalen **236** (1978), 95–104, especially
p. 103, the paragraph before Lemma 7.1, Lemma 7.1 and its proof, and p. 104,
the proof of Proposition 7.2. The entire article was read; pp. 96–104 were also
checked in page images to resolve extraction errors in signs and index sets.

| Original text | Lean correspondence |
| --- | --- |
| Projected simple roots and their dual weights, p. 103 | `roots`, `weights`, and the Kronecker-delta inner-product hypothesis |
| Nonpositive pairings of distinct projected simple roots, p. 103 | The hypothesis `i ≠ j → inner ℝ (roots i) (roots j) ≤ 0` |
| Vector orthogonal to the real Lie algebra of the split center, Lemma 7.1 | The vector belongs to the root span; this is represented by taking that span itself as `E` |
| Unique subset \(F(v)\), Lemma 7.1 | `∃! F : Finset ι` |
| Positive weight coefficients and nonnegative root coefficients, Lemma 7.1 | `0 < c i` on `F`, `0 ≤ d i` on its complement, and the displayed subtraction |
| Choice of a nonzero support of maximal cardinality, Proposition 7.2 | A later consumer of this proposition; no representation-theoretic exhaustion theorem is asserted here |

This is the finite Euclidean formulation justified explicitly by the proof of
Lemma 7.1: the argument uses the nonpositive pairings of distinct basis roots,
and the resulting nonnegative pairings of dual weights. Passing from the
source's ambient real parameter space to the orthogonal complement of its
central directions removes precisely the central component of the vector.
The root vectors form a basis of this complement. This specialization must be
established when the lemma is applied to a constructed reductive root datum or
to block parabolics of \(\mathrm{GL}_n\); the current proposition does not
postulate that geometric identification.

This statement has no project definition dependencies. Its environment is the
accepted environment artifact `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
with the pinned Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`.
Its only imported objects are Mathlib's real inner product spaces, bases,
finite sets, finite sums, and scalar multiplication.

The registered original is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
content SHA-256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`,
retained as `literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`.
The citation locator is printed p. 103, Lemma 7.1 and preceding paragraph/proof
(PDF page 9); its representation-theoretic use is printed p. 104,
Proposition 7.2 proof (PDF page 10).

Silberger attributes the proof to Langlands, *On the classification of
irreducible representations of real algebraic groups*, preprint,
Lemma 4.4, p. 87. The exact retained edition and its proof have been requested
under literature request `8adf3edf2a955df79dd1d7f9fbd54a34`.
The IAS-hosted retypesettings are leads with different pagination; they have
not yet been retained or identified with the cited preprint pagination.
This is an explicit transitive proof-source gap, not a claim that the result
is unproved in the literature. No Lean proof of the cone lemma or of the
Langlands quotient theorem is supplied by this proposition definition.
