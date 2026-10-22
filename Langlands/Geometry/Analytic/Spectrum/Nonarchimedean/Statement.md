# Strong triangle inequality for multiplicative seminorms

Author: Worker 36.

`Langlands.Analytic.SpectrumNonarchimedeanStatement` has two clauses.
First, a real-valued multiplicative ring seminorm p on any commutative
ring satisfies p(a + b) ≤ max(p(a), p(b)) if p(n) ≤ 1 for every natural
number n, mapped into that ring. Second, every actual bounded
multiplicative spectrum point of a normed commutative algebra over an
ultrametric normed field satisfies this strong triangle inequality.

The first clause assumes neither a norm on the ring nor that the seminorm
has zero kernel. The second permits independent universes for the algebra
and coefficient field. It assumes neither completeness nor an ultrametric
ambient algebra norm, and adds no strong triangle inequality to the
definition of a spectrum point. It asserts a property of every existing
point, without asserting that the spectrum is nonempty.

This is a derived prerequisite for the completed residue-field construction
following Exercise 1.2.4 in Berkovich's *Non-archimedean analytic spaces*
(Trieste 2009), p.4. The nonarchimedean inequality is stated at the beginning
of p.3, and Definition 1.2.3, p.4, defines spectrum points using the ordinary
triangle inequality. The source does not state the displayed two-clause
proposition separately. The general seminorm criterion follows by binomial
expansion: p(a + b)^n ≤ (n + 1) max(p(a), p(b))^n, and exponential growth
removes the factor n + 1. Scalar normalization at a spectrum point supplies
the required bound on natural numbers from the ultrametric coefficient
field. These arguments do not require completeness.

The criterion generalizes the normed-division-ring argument in the pinned
Mathlib module `Mathlib.Analysis.Normed.Field.Ultra`, specifically
`IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one`, to
possibly degenerate multiplicative seminorms on commutative rings.
The statement imports no proof of either clause and supplies no residue
field, analytic domain, or site construction.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`.
