# Bounded extension target for a rational presentation

Author: Worker 36.

`Langlands.Analytic.RationalPresentation.BoundedExtensionStatement`
asserts five properties of the actual closed-relation Tate quotient and
bounded base map in Definitions. The field K is complete and ultrametric,
and the base A is the presented quotient by the closure of the relations S.

Under the algebraic condition that the images of g and the f_j generate
the unit ideal in A, the image of g in the rational quotient is a unit.
Under the same condition, every base spectrum point satisfying
x(f_j) at most x(g) has x(g) nonzero. Independently of that condition,
every point of the rational quotient spectrum restricts to a point
satisfying these inequalities. This third clause is only forward inclusion.

The fourth clause asserts uniqueness: under the unit-ideal condition,
two bounded K-algebra maps from the rational quotient to a commutative
normed K-algebra B are equal if their restrictions to A agree. Neither
completeness nor ultrametricity of B is required for this clause.

The fifth clause adds completeness and ultrametricity of B. Given a
bounded map phi from A and a tuple b_j whose monomials have one positive
uniform norm bound, if phi(g) b_j = phi(f_j) for every j and the unit-ideal
condition holds, there exists exactly one bounded map from the rational
quotient restricting to phi. The tuple b supplies bounded solutions of
actual denominator equations; it is not an assumed extension map.
No power bounds are inferred from spectral inequalities here. The
extension formula on the new coordinates is a helper result of the
proof, not an additional clause of this proposition.

The field and target universes are independent. Zero variable counts,
zero quotients and zero target algebras are allowed, and no normalization
of the target unit norm is required. The construction uses the closure
of the generated ideal without assuming all Tate ideals are closed.

This is derived infrastructure for Berkovich's Trieste 2009
Exercise 2.2.2(ii), p.9. The source gives an affinoid-domain theorem from
absence of common spectrum zeros; this statement retains the algebraic
unit-ideal hypothesis and explicit bounded solutions into general complete
ultrametric normed targets. The unit-ideal condition implies absence of
common zeros because each spectrum kernel is proper. The converse,
reverse spectrum inclusion, relative-series identification, presentation
independence, and analytic-domain factorization are not asserted.
Definitions.md records the quotient conventions and exact source hash.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
