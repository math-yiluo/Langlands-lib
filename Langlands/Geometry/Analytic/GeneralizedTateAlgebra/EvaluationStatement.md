# Weighted evaluation and bounded universal property: exact target

Author: Worker 56.

`Langlands.Analytic.GeneralizedTateAlgebra.BoundedUniversalPropertyStatement`
is a proposition definition specifying three groups of obligations. This module
states them; it supplies no proof of convergence or of the universal property.
It uses the actual weighted restricted-series algebra, coordinate series `X`,
finite products `StrictTateAlgebra.monomialValue`, coefficient terms
`evaluationTerm`, and total infinite-sum formula `evaluate` from the imported
definitions.

In every clause, the variable type `σ`, coefficient field `K`, and target ring
`B` occupy independent universes. The polyradius assigns an arbitrary strictly
positive real radius to every variable. The field has an ultrametric norm and
is not assumed complete. The target is a normed commutative `K`-algebra.
Neither a finite variable type, a nontrivial valuation, nor radii in a value
group are required. The target can be the zero ring, and no `NormOneClass B`
assumption is made.

The first clause assumes that the target is complete and ultrametric and that
the tuple `b` has bounded weighted monomials. It asks for:

1. `HasSum` of the actual evaluated coefficient terms to `evaluate b f`, for
   every series `f`. Thus it asserts convergence, beyond a formal `tsum`
   equality.
2. The quantitative estimate `norm (evaluate b f) ≤ C * norm f` for every
   positive real `C` satisfying `norm (b^d) ≤ C * r.weight d` for all finitely
   supported natural exponents `d`. The constant is the supplied monomial
   bound, without an extra factor. The bound includes the empty monomial and
   hence already controls `norm (1 : B)`.
3. An actual `BoundedAlgHom K (GeneralizedTateAlgebra r K) B` which agrees with
   this infinite-sum formula on every series and sends each coordinate `X i`
   to `b i`.

The second clause requires neither completeness nor an ultrametric norm on the
target. It asks that the coordinate images of every bounded algebra
homomorphism satisfy the weighted monomial bound, and that two bounded algebra
homomorphisms with equal coordinate images are equal. These are conclusions,
not additional conditions imposed on a homomorphism. Coefficient completeness
is absent here as well.

The third clause returns to complete ultrametric targets. It asks for the exact
equivalence between the weighted monomial bound and the existence of a unique
bounded algebra homomorphism with prescribed coordinate images. This packages
the existence, necessity and uniqueness obligations above; it does not assume
an extension map or introduce a separate abstract algebra.

The intended analytic inputs are weighted coefficient decay and unconditional
monomial approximation in the source algebra. A positive monomial bound
controls each evaluated term by `C` times its weighted coefficient norm.
Polynomial approximation is expected to supply the algebra laws and
uniqueness. These observations explain the statement's derived scope and
minimal completeness hypotheses; they are not an implemented proof.
Finite-variable equivalence with separate power bounds and spectral-radius
criteria are outside this target.

The original mathematical context is Berkovich, *Non-Archimedean analytic
spaces* (Trieste lectures, 2009), Example 1.2.2(v), printed/PDF page 4, for
positive-polyradius restricted series and their weighted Gauss norm, and
Exercise 2.1.5(i), pages 7–8, for unique bounded extension into affinoid
algebras. These pages were read directly. The exercise uses finitely many
variables, an affinoid coefficient algebra, an existing bounded coefficient
map and spectral-radius bounds. This target is an internal field-coefficient
variant with arbitrary variable types, possibly incomplete coefficient field,
general complete ultrametric normed algebra targets, and explicit norm bounds
on all weighted monomials. It neither identifies these hypotheses with the
source's spectral condition nor claims the general relative-affinoid
extension theorem. Analytic domains and representability remain separate
constructions.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
