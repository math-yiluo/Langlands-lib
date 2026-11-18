# Polynomial finiteness for the Rosenlicht argument

Worker 565, 17 November 2026.

This internal commutative-algebra development supplies four proved helper
lemmas for the affine Rosenlicht units argument. It is not a translation of
a numbered theorem in the literature. All declarations are in
`Langlands.Algebra.Rosenlicht`.

`finite_of_degree_reductions` works over an arbitrary field `k`. Given a
surjective algebra map from a polynomial algebra in finitely many variables
to `R`, suppose each coordinate power `X i ^ n i` has the same image as a
polynomial `q i` of total degree strictly smaller than `n i`. Then `R` is
finite as a `k`-module. The implemented proof uses strong induction on
monomial degree. Monomials of degree at most the sum of the bounds `n i`
span the image. A larger monomial contains a reducible coordinate power;
replacing it decreases every resulting monomial degree. Finiteness of the
bounded-degree exponent vectors supplies a finite spanning set.

`homogeneousComponent_linear_mul` identifies the degree-`n` component of
`L * p`, where `L` is homogeneous of degree one and `1 ≤ n`, as `L` times
the degree-`n - 1` component of `p`. It specializes the graded direct-sum
multiplication theorem to the polynomial grading.

`finite_of_homogeneous_chart` assumes `k` is algebraically closed, `I` is
a homogeneous polynomial ideal, and `L` is homogeneous of degree one.
Its zero-locus hypothesis says that the common zeros of `I` and `L` consist
only of the zero vector. Any surjective algebra map annihilating `I` and
carrying `L` to one then has finite-dimensional target. The proof applies
Mathlib's algebraically closed field Nullstellensatz to `I + (L)`.
Each coordinate has a positive power in this ideal. Taking its matching
homogeneous component writes that power, modulo `I`, as `L` times a
polynomial of smaller degree. Mapping to the chart where `L = 1` gives
the degree reductions required by the first lemma.

`finite_points_of_homogeneous_chart` concludes that the set of `k`-points
annihilating `I` and carrying `L` to one is finite. Apply the preceding
lemma to the quotient by `I + (L - 1)`. Evaluation at such a point descends
to an algebra map from this finite-dimensional algebra to `k`.
There are finitely many such algebra maps, and the evaluations of the
coordinate generators make the map from points injective.

The direct imports are `Mathlib.RingTheory.Nullstellensatz`,
`Mathlib.RingTheory.MvPolynomial.Homogeneous`, and
`Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`. These provide the
Nullstellensatz, polynomial grading, bounded-exponent and finite-algebra
machinery used above; the degree-reduction and chart arguments are
implemented in this module.
