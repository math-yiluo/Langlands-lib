# The geometric endomorphism degree polynomial law

`Langlands.AbelianScheme.GeometricEndomorphismDegreePolynomialStatement`
is an unproved proposition definition, quantified in every universe `u`
over every algebraically closed characteristic-zero field `k : Type u`,
every actual abelian scheme `A` over `Spec k`, and every natural number
`g` for which `A.HasRelativeDimension g`. That last hypothesis is the
native smooth relative-dimension condition on the actual structure
morphism of `A`.

## Exact conclusions

The statement asserts the existence of a single function
`delta : End0 A → ℚ` with all of the following properties.

1. For every actual integral endomorphism `f : End A`,
   `delta (endToEnd0 A f) = (geometricEndomorphismDegree A f : ℚ)`.
2. `delta 1 = 1`.
3. For every pair of rational endomorphisms `a, b`,
   `delta (a * b) = delta a * delta b`.
4. For each `n : ℕ` and tuple `a : Fin n → End0 A`, there exists a
   multivariate polynomial `P : MvPolynomial (Fin n) ℚ` satisfying
   `P.IsHomogeneous (2 * g)`. For every tuple of rational scalars
   `x : Fin n → ℚ`, it satisfies
   `MvPolynomial.eval x P = delta (∑ i : Fin n, x i • a i)`.

`End0 A` is the published rationalization of the actual endomorphism
ring, carrying its native `ℚ`-algebra structure; `endToEnd0 A` is its
canonical unital ring map from `End A`. Multiplication is its native
composition product, `1` is the identity endomorphism, and `•` denotes
the rational module action. The displayed cast in conclusion 1 is the
canonical map from the natural-number-valued integral geometric degree
to `ℚ`. The sum ranges over all indices in `Fin n`.

The integral degree is imported from
`Langlands.AbelianScheme.GeometricEndomorphismDegree`. It uses the native
rank of the actual scheme morphism at its identity point in the isogeny
case, and zero otherwise. Its paired Markdown explains the point and
the underlying-morphism coercions.

Mathlib's native `MvPolynomial.IsHomogeneous` means that every monomial
with nonzero coefficient has total degree `2 * g`. It permits the zero
polynomial for every degree. In particular the conclusion covers
linearly dependent tuples, tuples on which degree vanishes, and the
empty tuple `n = 0`. The polynomial may depend on `n` and `a`, but the
same `delta` works for every tuple and every scalar choice. There is
no assumption that a tuple forms a basis or that a rational
endomorphism is invertible.

The existence of `delta`, its compatibility with the already constructed
integral degree, normalization, multiplicativity and polynomiality are
all conclusions. None is an additional hypothesis about `A`. The
existential form leaves denominator independence as part of the
unproved proposition rather than defining rational degree by an
unproved choice of denominators.

## Source and translation

The source is J. S. Milne, *Abelian Varieties* (1986 article, author revision
January 2, 2022), source ID
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The complete registered errata snapshot
`milne-abelian-varieties-1986-errata-2026-10-25` was read; its corrections
are incorporated in this revision. Printed and one-based PDF page
numbers coincide.

Section 12, top of p.21, defines integral degree and describes its
rational extension by clearing denominators. Proposition 12.4 on p.21
states that the extension is a homogeneous polynomial function of degree
`2 * g`. The polynomial-function definition preceding Lemma 12.3 on
p.20 uses finite linearly independent families. The all-tuples
formulation here is the equivalent pullback along a linear map:
express a finite tuple in a basis of its finite-dimensional span and
substitute the resulting linear forms into the homogeneous polynomial.
Such a substitution preserves homogeneity in the native convention,
including a zero polynomial.

Normalization and multiplicativity are source-derived properties
packaged with polynomiality. Section 8, Proposition 8.1 and its
following paragraph on p.12 identify isogeny degree with finite locally
free rank and give multiplicativity under composition. Identity degree
is one. Extending degree by zero to nonisogeny endomorphisms and then
clearing denominators gives the corresponding multiplicativity and
normalization on `End0 A`. These conclusions remain proof obligations
of the present statement.

The discussion before Proposition 12.9 on p.23 applies Proposition 12.4
to a one-parameter family to obtain the geometric characteristic
polynomial. It motivates the present prerequisite. This statement
contains no trace or Tate comparison assertion. Algebraic closedness
and characteristic zero are deliberate restrictions of the source's
more general field scope, matching the intended consumer. The present
module supplies the exact proposition to be proved in a separate
focused proof task; it does not prove any of its conclusions.
