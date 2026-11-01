# Polynomial evaluation and trace comparison on actual Cartan spaces

Author: Worker 94. Module:
`Langlands.Global.ArchimedeanCartanPolynomialDuality`. All public
declarations lie in `Langlands.Global.ArchimedeanGL`. The constructions
apply to every `K : Type u` with `Field K` and `NumberField K` and every
natural rank `n`, including zero.

This is an internal construction from the actual spaces and trace
equivalences in `ArchimedeanCartanTraceDuality`, using Mathlib's symmetric
algebra, finite-dimensional duality, and multivariate polynomial
extensionality over the infinite field of complex numbers. It makes no
appeal to an external invariant-theory theorem.

`LiePolynomialAlgebra` is the complex symmetric algebra on the algebraic
dual of the actual full complex Lie algebra. `CartanPolynomialAlgebra`
is the corresponding symmetric algebra on the dual of the actual
complexified self-adjoint Cartan complement. The two
`PolynomialEvaluation` algebra homomorphisms are the symmetric lifts of
evaluation of a linear functional at a vector. Thus evaluation of the
generator associated to `f` at `X` is exactly `f X`.

The two `Polynomial_ext` theorems prove that evaluations at all actual
vectors separate these symmetric tensors. First, a private generic lemma
chooses a finite basis and presents its symmetric algebra as a
multivariate polynomial algebra. Every tuple of generator values is
realized by a linear functional, using the basis constructor. Evaluation
of the symmetric tensor agrees with multivariate evaluation, by equality
of algebra homomorphisms on the basis. Mathlib's infinite-field polynomial
extensionality then proves equality of tensors. Applied to the dual space,
finite-dimensional double-dual surjectivity says that every linear
functional on the dual is evaluation at a vector of the original space.
This gives the stated extensionality results, including in dimension zero.

`lieSymmetricTraceEquiv` and `cartanSymmetricTraceEquiv` lift the two actual
trace-duality linear equivalences to complex algebra equivalences between
symmetric algebras on vectors and on duals. The private symmetric-map
construction uses the universal property. Lifting the inverse linear map
gives the inverse algebra map, since their compositions fix every
generator. The public generator formulas specify the maps explicitly.

`cartanPolynomialRestriction` is the symmetric lift of precomposition of
linear functionals with `cartanComplexInclusion`. Its evaluation theorem
states that evaluating a restricted polynomial at a complementary vector
equals evaluating the original polynomial at that vector's actual full
inclusion. `cartanSymmetricTraceEquiv_projection` proves the commuting
comparison: symmetric projection on vectors corresponds under the trace
equivalences to this polynomial restriction. This follows from the
previous unit's projection-versus-dual-restriction identity on each
generator and symmetric-algebra extensionality.

`liePolynomialConjugation` lifts precomposition of functionals with the
inverse full-group conjugation. `cartanPolynomialConjugation` does the
same for the entire standard compact subgroup on the complementary
space. Their evaluation formulas state
`(g.P)(X) = P(Ad(g^{-1}) X)`. Polynomial extensionality and the actual
vector conjugation laws prove the identity and product laws; applying a
group element to the inverse product identity proves the inverse law.
The product convention is
`action(g*h) = action(h).trans(action(g))`, so it acts on a polynomial
by first applying `h` and then `g`.

`cartanPolynomialRestriction_conjugation` proves equivariance of
restriction for every compact element. It uses evaluation extensionality,
the two action-evaluation formulas, and equivariance of the actual
inclusion. Finally the two `SymmetricTraceEquiv_conjugation` theorems
extend trace-duality equivariance from vectors to the symmetric algebras
by checking the generators. The full-space theorem quantifies over every
actual archimedean general linear group element; the complementary
theorem quantifies over the full standard compact subgroup.

These results justify treating the dual symmetric tensors as evaluated
polynomials on the actual spaces and identify their restriction and
actions with the vector-symmetric constructions. Finite generation of
compact invariants over restricted full-group invariants, PBW, central
generation, admissibility, and the final automorphic differential-growth
theorem remain separate obligations.

The local real finite-dimensionality instance is explicitly named for this
module, so separate prerequisite branches can be imported together without
colliding generated declaration names. Its type and proof are unchanged.
