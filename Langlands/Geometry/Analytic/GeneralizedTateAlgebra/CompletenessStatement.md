# Completeness of positive-polyradius restricted power series

Author: Worker 56.

`Langlands.Analytic.GeneralizedTateAlgebra.CompletenessStatement r K`
asserts that the actual normed ring `GeneralizedTateAlgebra r K` is a
complete space for its weighted Gauss norm. Its parameters are an arbitrary
variable type, a positive real polyradius, and an ultrametric normed
commutative coefficient ring. The proposition explicitly binds
`CompleteSpace K`; it does not assert completeness for incomplete
coefficients. Its conclusion uses the norm and uniform structure already
constructed in `GeneralizedTateAlgebra.Definitions`.

All radii are strictly positive real numbers, with no requirement that they
belong to a coefficient field's value group. There is no finiteness or
nonemptiness assumption on the variable type, no nontriviality assumption
on the coefficient ring, and no assumption of a nontrivial valuation.
Consequently empty variable types, the zero coefficient ring, and complete
trivially valued fields are included. Over a complete ultrametric normed
field, this target supplies the missing completeness property of the
already constructed normed algebra.

For finitely many variables over a complete nonarchimedean field, this is
the completeness assertion in Berkovich, *Non-Archimedean analytic spaces*
(Trieste lectures, 2009), Example 1.2.2(v), printed/PDF page 4.
Definition 2.1.6(i), page 8, gives the relative Banach algebra formula.
The registered original is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
Pages 4 and 8 were read again when preparing this target.

The arbitrary-variable and coefficient-ring scope is a derived extension,
not a literal statement of the source. The carrier uses cofinite decay of
weighted coefficients. A proposed direct proof takes coefficientwise
limits of a Cauchy sequence, uses positivity of each monomial weight to
obtain coefficient convergence, and passes the uniform weighted estimates
to the limit. Comparing with one restricted series then gives cofinite
decay and convergence in the Gauss norm. This explains the intended
generalization; no proof or completeness instance is provided by this
statement file.

The target does not assert Noetherianity, that all ideals are closed, or
any affinoid presentation or domain property. Those are separate
construction and theorem obligations.
