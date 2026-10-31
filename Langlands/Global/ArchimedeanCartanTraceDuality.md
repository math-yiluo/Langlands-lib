# Trace duality of the actual complex Cartan spaces

Author: Worker 94. Module:
`Langlands.Global.ArchimedeanCartanTraceDuality`. All declarations are in
`Langlands.Global.ArchimedeanGL`. The construction applies to every
`K : Type u` with `Field K` and `NumberField K`, and every natural rank `n`,
including zero.

These are internal finite-dimensional linear-algebra constructions, using the
published coordinate trace and Cartan decomposition. The imports
`ArchimedeanCartanTraceForm` and `ArchimedeanCartanSymmetricAlgebra` retain the
actual matrix carriers, self-adjoint complement, scalar extensions,
inclusion/projection and conjugation maps. No external existence theorem
or new topology on these carriers is used.

`cartanTraceForm` restricts `matrixTraceForm` to the self-adjoint real
complement. Its symmetry is inherited. On a vector paired with itself it is
the published positive Cartan form, so the positive-form zero criterion
proves both sides of nondegeneracy.

`complexMatrixTraceForm` and `complexCartanTraceForm` are Mathlib's bilinear
base changes to the complex numbers. Their pure tensor formulas are
`B_C(z tensor X, w tensor Y) = B(X,Y) • (z*w)`, with the real value acting
by scalar multiplication on the complex coefficient. These are complex
bilinear forms, with no conjugation of either tensor coefficient.

A private finite-dimensional lemma proves nondegeneracy after complex
scalar extension. Choose a real finite basis `b` and its trace-dual basis
`d`. Pairing an extended vector with `1 tensor b(i)` recovers its `i`th
coordinate in `d.baseChange C`, by tensor induction. If all pairings
vanish, all coordinates vanish and the vector is zero. Symmetry of the
base-changed form gives separation on the other side. The actual real
matrix equivalence supplies finite dimension from the finite archimedean
matrix coordinates; the complement is a submodule. This argument includes
the zero-dimensional case.

`complexTraceDualEquiv` and `cartanTraceDualEquiv` apply Mathlib's
`BilinForm.toDual` to the two nondegenerate complex forms. Their value at
`X`, evaluated on `Y`, is exactly the corresponding trace pairing. Thus
these are explicit complex linear equivalences with the complex algebraic
duals.

`matrixTraceForm_conjugation` proves invariance under the entire actual
general linear group. Multiplication of the two conjugated matrices
cancels the adjacent inverse and matrix; matrix trace is invariant under
conjugation. Double tensor induction gives
`complexMatrixTraceForm_conjugation`. No connectedness assumption is used.

`matrixTraceForm_cartanProjection` decomposes its first argument into
compact and complementary parts. The compact part pairs to zero with a
complementary second argument, by the published positive-form orthogonality.
Double tensor induction then proves
`complexMatrixTraceForm_cartanProjection`: pairing a full vector with the
inclusion of a complementary vector equals the complementary pairing of
its projection with that vector. Composing with inclusion in the first
argument gives `complexMatrixTraceForm_cartanInclusion`.

Inclusion equivariance and full trace invariance prove
`complexCartanTraceForm_conjugation` for every element of the full standard
compact subgroup. The two `TraceDualEquiv_conjugation` lemmas express the
contragredient convention explicitly: the functional associated to
`Ad(g) X` is the functional associated to `X` composed with `Ad(g^{-1})`.
For the complement, `g` ranges over the entire standard compact subgroup.
Finally, `cartanTraceDualEquiv_projection` states equality of functionals:
the complementary trace functional of the projection of `X` is the full
trace functional of `X` restricted along the actual inclusion.

This unit establishes vector-space trace duality and its equivariant
projection comparison. Symmetric-algebra comparison, polynomial evaluation
injectivity, invariant restriction finiteness, PBW, central generation and
the final automorphic growth theorem remain separate obligations.
