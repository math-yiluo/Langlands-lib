# Scalar change of variables for local-field Haar integrals

`Langlands.HarmonicAnalysis.localFieldScalarHaarIntegral` proves
`LocalFieldScalarHaarIntegralStatement`. For a nonarchimedean local field \(F\),
a Borel additive Haar measure \(\mu\), a field unit \(a\), and a complex
Schwartz–Bruhat function \(f\), it gives
\[
\int_F f(ax)\,d\mu(x) = |a|_F^{-1}\int_F f(x)\,d\mu(x),
\qquad |a|_F=q^{-v_F(a)}.
\]
Here \(q\) is the cardinality of the residue field.

Multiplication by \(a\) is continuous and hence Borel measurable. The local
constancy of \(f\) gives continuity and thus strong measurability.
`integral_map_of_stronglyMeasurable` then rewrites the left side as the
integral of \(f\) against the pushforward of \(\mu\) by \(x\mapsto ax\).
`Langlands.BaseChange.map_mul_residueAbsolute` identifies this pushforward
with \(|a|_F^{-1}\mu\), using the fact that \(a\) is nonzero.
`integral_smul_nnreal_measure` moves the nonnegative coefficient outside the
integral. `NNReal.coe_inv` identifies its real coercion with the inverse
residue-normalized absolute value acting on the complex integral.

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, § V.1, printed pp. 103–104 (PDF pp. 109–110).
The normalization is on p. 103 and the integral identity is on p. 104.
The source is registered as
`renard-2026-representations-groupes-reductifs-padiques` with SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
