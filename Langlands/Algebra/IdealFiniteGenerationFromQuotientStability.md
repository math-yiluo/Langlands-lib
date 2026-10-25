# Finite generation from quotient stability: proof

`Langlands.Algebra.idealFiniteGenerationFromQuotientStability` proves the complete
published proposition
`Langlands.Algebra.IdealFiniteGenerationFromQuotientStabilityStatement`.
The commutative rings \(B\) and \(F\) have independent universe levels. The theorem
adds no hypotheses to the statement.

Let \(f:B\to F\) be a ring homomorphism and \(J\) an ideal of \(B\). Suppose
\(J.\mathrm{map}(f)\) is finitely generated and that, for all finitely generated
ideals \(I\subset K\subset J\) with \(I.\mathrm{map}(f)=J.\mathrm{map}(f)\),
the canonical quotient map \(B/I\to B/K\) is injective. The theorem concludes
that \(J\) is finitely generated.

The Lean proof uses `Submodule.fg_span_iff_fg_span_finset_subset` to choose a
finite subset of \(f(J)\) whose ideal span is \(J.\mathrm{map}(f)\).
`Set.exists_subset_image_finite_and` lifts that subset to a finite set
\(t\subset J\). Set \(I=\operatorname{Ideal.span}(t)\). The finite span is
finitely generated, \(I\subset J\), and `Ideal.map_span` gives
\(I.\mathrm{map}(f)=J.\mathrm{map}(f)\). This step uses the definition of an
extended ideal as an ideal span; it does not assume that the image set
\(f(J)\) itself is an ideal.

For each \(x\in J\), form \(K=I+\operatorname{Ideal.span}\{x\}\).
Finite generation is preserved by this sum, and \(I\subset K\subset J\).
The supplied injectivity of the actual map `Ideal.Quotient.factor hIK`,
together with `Ideal.Quotient.factor_mk`, shows that the class of \(x\)
modulo \(I\) is zero, because its class modulo \(K\) is zero.
`Ideal.Quotient.eq_zero_iff_mem` therefore gives \(x\in I\).
Consequently \(I=J\), and finite generation transfers along that equality.

This is a derived elementary argument from the finite image generators and
final comparison of finite quotients in Stacks Lemma 10.128.9,
[tag 05UV](https://stacks.math.columbia.edu/tag/05UV). The registered original
is `stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `05UV.html`. The source's repeated \(J'\) in the final nested containment
is read as \(J'\subset J''\subset J\), as in the published statement.
The proof isolates this elementary step from the flatness results that supply
quotient injectivity in the source. It requires neither surjectivity of \(f\)
nor Noetherianity, locality, nontriviality, or flatness.
