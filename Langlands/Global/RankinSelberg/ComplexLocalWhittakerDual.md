# Inverse transpose on the complex local Whittaker model

For a list `ds` of `r + 1` characters, `ComplexLocalWhittakerDualStatement`
says that inverse-transpose pullback sends a function in
`complexWhittakerModel r ds a` to the model for the reversed inverse list
`dualData ds` and additive parameter `-a`. The theorem `dualFunction_mem` proves
this for the exact pullback \(g \mapsto W(w_0(g^{-1})^{\mathsf T})\) used in the
local Rankin–Selberg integrals.

On the upper-Borel standard modules, the proof uses the published
`ComplexTransposeStandardDuality.twistEquiv`. It conjugates a Whittaker
intertwiner by the inverse of that equivalence on its source and by pullback
on its values. Conjugating the inverse transpose of an upper unipotent matrix
by \(w_0\) reverses and negates its adjacent upper entries. The sum therefore
changes sign, which gives equivariance for `-a`. Smoothness follows from the
smooth pullback, and the growth bound uses the same constants because the
twist swaps the entry-square sums for \(g\) and \(g^{-1}\) up to reindexing.
The published identities for this pullback carry the right compact action
through \(k\mapsto(k^{-1})^{\mathsf T}\) and the right Lie derivative through
\(X\mapsto-X^{\mathsf T}\). The proof then applies the submodule comap
criterion to each intertwiner range in the model's defining supremum.

This is an internal transfer lemma on the Library's compact-finite carrier.
The formula for the dual function and its opposite Whittaker character are
used in Jacquet's local integrals. [Jacquet, *Archimedean Rankin–Selberg integrals*, pp. 4–6](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
