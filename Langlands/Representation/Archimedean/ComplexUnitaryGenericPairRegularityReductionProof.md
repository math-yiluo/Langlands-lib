# Proof: reduction of the complex case of Getz–Hahn, Theorem 11.5.2

Module `Langlands.Representation.Archimedean.ComplexUnitaryGenericPairRegularityReductionProof`
proves

```lean
theorem Langlands.Archimedean.complexUnitaryGenericPairRegularityReduction :
    ComplexUnitaryGenericPairRegularityReductionStatement.{uV, uW}
```

The target is the published proposition
`Langlands.Archimedean.ComplexUnitaryGenericPairRegularityReductionStatement` of module
`Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement`, unchanged and
with its universe parameters `uV`, `uW`:

```lean
ComplexUnitaryGenericExponentBoundStatement.{uV} →
  ComplexUnitaryGenericExponentBoundStatement.{uW} →
    ComplexPairLFactorRightHalfPlaneRegularityStatement →
      ComplexUnitaryGenericPairRegularityStatement.{uV, uW}
```

The exponent bound at both carrier universes and the right half-plane regularity of complex pair
`L`-factors together imply the complex case of Getz–Hahn, Theorem 11.5.2. For irreducible admissible
generic unitarizable `(𝔤𝔩_n(ℂ), U(n))`- and `(𝔤𝔩_m(ℂ), U(m))`-modules
with standard parameters `ds`, `ds'`, the denominator `P` of `complexPairLFactor ds ds'`
satisfies `P(s) ≠ 0` whenever `1 ≤ s.re`.

The module imports only the statement module. All three inputs are hypotheses of the
statement, and none is proved here. The theorem uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The proof follows step 4 of "Why the statements are true" in the statement Markdown.

1. Introduce the exponent bounds `hV` (universe `uV`) and `hW` (universe `uW`), the
   regularity hypothesis `hreg`, the two modules with all their hypotheses, and `s` with
   `1 ≤ s.re`.
2. Apply `hreg ds ds' s`. It remains to show
   `0 < s.re + x.exponent.re + y.exponent.re` for `x ∈ ds` and `y ∈ ds'`.
3. The bound `hV`, applied to the first module (carrier `V : Type uV`) and its six hypotheses,
   gives `|x.exponent.re| < 1/2`. The bound `hW`, applied to the second module
   (carrier `W : Type uW`), gives `|y.exponent.re| < 1/2`. By `abs_lt`, both
   exponents are `> −1/2`.
4. Hence `s.re + x.exponent.re + y.exponent.re > 1 − 1/2 − 1/2 = 0` (`linarith`).

## Provenance

The conclusion is the archimedean case of J. R. Getz and H. Hahn (2024), *An introduction to
automorphic representations* (`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), Theorem 11.5.2, p.305
(PDF 316). The setup of §11.5 is on p.304 (PDF 315). Getz–Hahn do not prove the archimedean
case themselves; they refer to [BR94a, §2] (Barthel–Ramakrishnan 1994), which is not in the
project literature and is not used here. The implemented route is the argument recorded in
step 4 of "Why the statements are true" in the statement Markdown. The bound
`|Re t| < 1/2` on the exponents of generic unitary modules gives
`Re(s) + Re(t) + Re(t') > 0` on `Re(s) ≥ 1`, and then the elementary regularity of the
`Γ`-factors applies. The statement Markdown records the sources of the bound:
Badulescu–Renard (2010), Theorem 8.2, for `GL_n(ℝ)`, and a derived adaptation for
`GL_n(ℂ)`. In this module both the bound and the regularity are hypotheses, and the proof is
only the arithmetic of step 4.
