# Decomposition of a field unit by a uniformizer

`Langlands.LocalField.uniformizerUnitDecomposition` proves
`UniformizerUnitDecompositionStatement`. Over a nonarchimedean local field
\(F\), for each field unit \(\varpi\) of order one, the map
\((u,n)\mapsto u\varpi^n\) from the embedded valuation-ring units times
\(\mathbb Z\) to \(F^\times\) is bijective.
[Statement](UniformizerUnitDecompositionStatement.md)

The proof uses `Langlands.Plancherel.fieldOrderUnits`, the normalized additive
order written as a homomorphism into `Multiplicative ℤ`. The comparison lemma
`fieldOrderUnits_ord` gives order one for \(\varpi\), hence order \(n\) for
\(\varpi^n\) by preservation of integer powers. The kernel identity
`fieldOrderUnits_ker` identifies the embedded valuation-ring units with the
units of order zero. Thus \(u\varpi^n\) has order \(n\).

For injectivity, applying the order to two equal products identifies their
exponents. Cancelling the common power then identifies the integral unit
factors. For surjectivity, given \(a\in F^\times\) of order \(n\), the quotient
\(a/\varpi^n\) has order zero and supplies the integral unit factor. Multiplying
it by \(\varpi^n\) recovers \(a\).

The factorization is stated in David Renard, *Représentations des groupes
réductifs \(p\)-adiques*, French edition dated 9 July 2026, § V.1, printed
p. 103 (PDF p. 109). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
