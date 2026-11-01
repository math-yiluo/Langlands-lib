# A test-independent Mellin convergence threshold

Worker 468, reusing the published Mellin telescope authored by Worker 331.
This is an internal Prop-valued statement, with no proof supplied.
It strengthens the convergence quantifier in the published
`FiniteFunctionMellinStatement` and adds no rationality or denominator claim.

`Langlands.RankinSelberg.UniformFiniteFunctionMellinConvergenceStatement`
quantifies over every prime, p-adic field `F : PadicField.{uF} p`, supplied
topological data `T : F.TopologicalData`, natural dimension `r`, positive
integral weights `m : Fin r → ℕ`, and finite family `X` of continuous complex
functions on `A = Fin r → F.Carrierˣ` with finite-dimensional left-translation
span. It installs the supplied topology, valuation, local-field structure and
Borel measurable structures on the field and units. The product torus has its
product measurable structure and actual product measure

```text
dA = Measure.pi (fun _ : Fin r => localMultiplicativeHaar F.Carrier).
```

For every member `η` and arbitrary Schwartz--Bruhat function `Φ` on the full
additive space `Fin r → F.Carrier`, the integrand is exactly

```text
Φ((↑(a i))ᵢ) * η(a) * prod_i (T.normalizedAbs ↑(a i) : ℂ)^((m i : ℂ) * s).
```

The conclusion chooses **one real `c` before `η`, `Φ` and `s`**, and asserts
Bochner integrability for every `η ∈ X`, every such `Φ`, and every complex `s`
with `c < s.re`. The bound may depend on `F`, `T`, `r`, `m` and `X`, but never
on the test function. All dimensions including zero and the empty family are
included. Positivity of every weight is retained. There is no restriction to
decomposable test functions or to one fixed compact support.

The published `FiniteFunctionMellinStatement` uses the same functions,
weights, tests and measure, but chooses its convergence threshold after the
test function. Its rational-continuation and common-denominator conclusions
remain separate available results. Neither that pointwise assertion nor its
uniform denominator alone supplies this proposition.

This is derived internal support for common convergence of matrix integrals
on actual Whittaker quotient models in the two-block rank-one analytic base.
Its proposed derivation uses the finite-dimensional translation span: take a
finite basis of translates (or their linear combinations), apply the existing
pointwise Mellin convergence theorem to one fixed compact clopen unit-box test
and that finite basis, and intersect the finitely many half-planes. Dilate the
compact support of an arbitrary test into that box. Multiplicative Haar
invariance, the factored determinant weight and stability of the finite span
under translation then reduce integrability to the fixed-box basis estimates
by finite sums and norm domination. The threshold does not change under the
dilation; only finite scalar factors do. This paragraph gives the rationale
and remaining proof obligation, not an implemented proof or a literal claim
of a named literature theorem.

No matrix convergence, normalized generator, functional equation, factor
existence, irreducibility, or two-block analytic base is assumed or concluded.
The statement does not alter the published pointwise Mellin pair or anything
in the host targets' import closure.
