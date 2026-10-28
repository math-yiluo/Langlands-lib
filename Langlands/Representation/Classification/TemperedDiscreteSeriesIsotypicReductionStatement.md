# Reduction of discrete-series isotypic projectors to exponents below two

The closed proposition
`Langlands.GLTemperedDiscreteSeriesIsotypicReductionStatement.{uF,uV,uW}` is exactly

```lean
GLProductLeviSquareIntegrableLpStatement.{uF, uW} →
  GLTemperedDiscreteSeriesIsotypicStatement.{uF, uV, uW}
```

Both propositions are imported unchanged. The premise is stated in
[ProductLeviSquareIntegrableLpStatement](ProductLeviSquareIntegrableLpStatement.md):
every absolute coefficient of an irreducible square-integrable-mod-centre
representation of an actual standard block Levi lies in `L^r` of the actual
central quotient for some `1 < r < 2`. The conclusion is the full projector
statement of
[TemperedDiscreteSeriesIsotypicStatement](TemperedDiscreteSeriesIsotypicStatement.md).
It has the same fields, block Levis, topologies, Borel Haar measures,
independent universes `uF`, `uV`, `uW`, analytic predicates, central-character
data and conclusion. The premise is instantiated at the universes `uF` and `uW`
of the field and of the square-integrable representation `σ`.

This is an internal reduction target. It neither proves its premise nor
replaces the unconditional target. The intended proof uses the premise only to
make the integral over the central quotient of a coefficient of `σ` times a
coefficient of the tempered `ρ` absolutely convergent. Hölder's inequality is
applied with the exponents `r` and `r / (r - 1) > 2`. The rest of the intended
proof is algebraic or uses existing Library results: right invariance of Haar
measure on the central quotient, the invariant form attached to `σ`, extension
of smooth functionals, smooth biduality, finiteness of intertwiner spaces and
Schur's lemma. Its provenance is the proof of Silberger 1979, Theorem 4.5.18,
which adapts Theorem 3.3.1. The analytic estimate there is replaced by the premise. That premise is
derived from the proof of Waldspurger 2003, Corollary III.1.2, as explained in
its own Markdown file.
