# Trace and positive Cartan forms on the actual matrix Lie algebra

Authors: Worker 94 and Worker 459. Module:
`Langlands.Global.ArchimedeanCartanTraceForm`. All declarations are in
`Langlands.Global.ArchimedeanGL`.

The construction retains the published
`RealLieAlgebra K n` and its matrix coordinates, star, compact Lie subalgebra
and Cartan complement. It applies to every number field in every universe
and every natural rank, including zero.

`totalMixedTrace` sums real coordinates with weight one and real parts of
complex coordinates with weight two. The latter weight is the scalar trace
of a complex multiplication map on its two-dimensional underlying real
space. This normalization is fixed explicitly by the defining formula.
No identification with the trace of a real linear endomorphism is claimed:
the normalization is part of the explicit definition.

`matrixTraceForm` is the real bilinear form obtained by applying this scalar
functional to the matrix trace of the product. Its symmetry follows from
cyclicity of matrix trace. Its commutator invariance expands both brackets,
uses distributivity and rotates a triple product inside the trace.
Conjugate transpose reverses products, and the scalar functional preserves
star; these facts prove star invariance.

`cartanPositiveForm X Y` is `matrixTraceForm X (star Y)`, equivalently the
negative of `matrixTraceForm X (cartanInvolution Y)`. Its symmetry follows
from symmetry and star invariance of the original form. This construction
adds no topology, norm or global inner-product instance to the original
carrier. In particular, the existing operator matrix norm and mixed-space
topology retain their published meanings.

`totalMixedTrace_mul_star` computes the scalar functional on `a * star a`
as the sum of squared real coordinates plus twice the sum of the complex
norm squares. Every summand is nonnegative. If the result is zero, both
outer sums vanish, and the nonnegative finite-sum zero criterion makes
each coordinate zero. Complex norm-square vanishing retains both the real
and the imaginary direction.

`cartanPositiveForm_self_sum` expands the matrix trace and multiplication
and moves the linear functional through both finite sums. The resulting
entrywise scalar formula gives the exact identity

```text
Q(X,X) = sum_i sum_j
  (sum_real_v (A(X) i j).real(v)^2
   + 2 * sum_complex_v normSq((A(X) i j).complex(v))),
```

where `A` is the unchanged `realLieAlgebraToMatrix`. The declaration
`cartanPositiveForm_self_coordinates` states this identity in Lean.
`cartanPositiveForm_self_nonneg` and
`cartanPositiveForm_self_eq_zero_iff` prove nonnegativity and that zero
occurs exactly for the zero matrix. The latter proof applies the
nonnegative finite-sum criterion twice, then the scalar zero criterion,
and finally injectivity of the matrix-coordinate equivalence.
`cartanPositiveForm_self_pos` concludes strict positivity for a nonzero
vector.

Both forms are nondegenerate in Mathlib's two-sided sense. For the original
trace form, testing a vector against its star reduces separation to the
positive-form zero criterion; symmetry handles the other side. For the
positive form, testing a vector against itself proves both sides directly.
These arguments require no nonzero vector or positive-rank hypothesis.
At rank zero all matrix sums are empty, the vector space has only its zero
element, and the nondegeneracy conclusions hold with their usual vacuous
meaning.

The published compact Lie subalgebra consists of `star X = -X`, and the
published Cartan complement consists of `star Y = Y`. Substituting these
identities in the definition proves `B(X,Y) = -Q(X,Y)` when the right
argument is compact and `B(X,Y) = Q(X,Y)` when it is complementary.
The conclusions therefore apply, in particular, on each respective
subspace. For a compact `X` and complementary `Y`, star invariance makes
`B(X,Y)` equal to its own negative; it is zero over the reals. This proves
`Q(X,Y) = 0`. Symmetry supplies the reversed orthogonality statement.

These are internal elementary matrix constructions, derived from the
coordinate formulas, linearity, finite sums, cyclicity of trace and complex
conjugation. They invoke no external general existence theorem. No Casimir,
differential symbol, analytic regularity or final automorphic-growth proof
is claimed.
