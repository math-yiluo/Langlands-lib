# Shell generating integrals of finite functions

`Langlands.RankinSelberg.FiniteFunctionShellSeriesStatement.{uF}` is a
closed Prop-valued definition. It states a derived internal step in the
valuation-shell route to `OneVariableMellinStatement`. The module supplies
the proposition only, with no proof of its recurrence or analytic conclusions.
Its sole new public declaration is the proposition; all auxiliary functions,
sets, measures and witnesses remain local.

Worker 351 authored this pair using Worker 656's supplied formulation.

## Quantifiers and actual objects

The proposition quantifies over every prime `p` with `Fact p.Prime`, every
`F : PadicField.{uF} p` and every supplied `T : F.TopologicalData`. The
field universe `uF` is arbitrary. Its local instances are exactly those
of `OneVariableMellinStatement`, in the same order: `T.topology`,
`T.valuativeRel`, `T.localField`, `borel F.Carrier` and its `BorelSpace`
witness, then `borel F.Carrierˣ` and its `BorelSpace` witness. The unit
group has the induced units topology.

For every `η : F.Carrierˣ → ℂ`, the only hypotheses on `η` are continuity
and finite dimensionality over `ℂ` of the actual left-translation span

```text
Submodule.span ℂ
  (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a)).
```

Two local let-bindings fix the actual normalized multiplicative Haar
measure and the actual integral units:

```text
μ := localMultiplicativeHaar F.Carrier
K := (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ).
```

Thus `μ` is the measure of `RankinSelberg.Measures`, whose integral units
have mass one (`localMultiplicativeHaar_integerUnits`), and `K` is the unit
group of the valuation integer ring, viewed inside the field's units.
`T.ord` is the actual normalized integer order. No replacement measure,
coefficient sequence or order is an input.

After these hypotheses and let-bindings, the quantifier order is

```text
∃ π : F.Carrierˣ, ∃ E : LinearRecurrence ℂ, ∃ B : ℝ,
  T.ord (↑π) = 1 ∧ 1 ≤ B ∧
  ∀ Φ : HarmonicAnalysis.SchwartzBruhat F.Carrier,
    let c : ℤ → ℂ := …
    ∃ L : ℤ, ∃ N : ℕ,
      L ≤ (N : ℤ) ∧ lower_support_bound ∧ recurrent_tail ∧
      ∀ z : ℂ, z ≠ 0 → B * ‖z‖ < 1 → analytic_conclusions.
```

One uniformizer `π`, recurrence `E` and real bound `B` therefore serve
every test function and every allowed `z` for the fixed field data and
finite function. The witnesses `L,N` may depend on `Φ`, and are chosen
before `z`. The same witnesses occur with both the recurrence and
analytic conclusions. The statement does not demand that the choice of
`π` be independent of `η`.

## Coefficients, support and recurrence

For each test function `Φ`, the coefficient is defined exactly by the
Bochner set integral

```text
c n = ∫ u in K, Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) *
                   η (π ^ n * u) ∂μ,       n : ℤ.
```

The power of `π` and the multiplication take place in the unit group,
followed by coercion to the field for evaluation of `Φ`. The set integral
uses `μ` restricted to `K`. This is an actual integral of the specified
functions, rather than an abstract sequence supplied with recurrence or
growth assumptions.

For this sequence there are `L : ℤ` and `N : ℕ` such that:

1. `L ≤ (N : ℤ)`;
2. `c n = 0` for every integer `n < L`;
3. `E.IsSolution (fun j : ℕ => c ((j : ℤ) + (N : ℤ)))`.

The recurrence is Mathlib's existing `LinearRecurrence ℂ`. For
`a j := c ((j : ℤ) + (N : ℤ))`, its solution condition means

```text
a (j + E.order) = ∑ i : Fin E.order, E.coeffs i * a (j + i)
```

for every `j : ℕ`. There is no positivity restriction on `E.order` and
no nonzero-dimension hypothesis on the translation span. Order zero and
the identically zero finite function are included. The proposition does
not require a minimal recurrence or a particular order.

The tests range over the full Schwartz–Bruhat space on the field: compactly
supported locally constant complex functions, including those with
`Φ 0 ≠ 0`. There is no hypothesis `Φ 0 = 0`. Only the negative tail of
`c` must vanish; an infinite recurrent positive tail is permitted.

## Actual integrability and bilateral sum

For every nonzero complex `z` satisfying `B * ‖z‖ < 1`, three conclusions
hold:

1. `MeasureTheory.Integrable` holds for the function on `F.Carrierˣ`
   given by `a ↦ Φ (a : F.Carrier) * η a * z ^ (T.ord (a : F.Carrier))`,
   against the actual measure `μ`.
2. `Summable (fun n : ℤ => c n * z ^ n)` holds in `ℂ`.
3. The actual Bochner integral of that same function equals
   `∑' n : ℤ, c n * z ^ n`.

The powers of `z` are integer powers, including negative exponents.
The nonzero condition excludes their singular point. Since `1 ≤ B`,
the inequality describes a punctured disc of positive radius `1/B`
chosen uniformly over all `Φ`. `Summable` and `tsum` use Mathlib's
unconditional summation over `ℤ`. The explicit integrability conclusion
is stronger than merely writing an equality involving a totalized
Bochner integral.

Neither growth nor summability of `η` is an additional hypothesis.
The proposition contains no rational continuation, spectral substitution,
polynomial or Laurent denominator, or final Mellin half-plane assertion.
Those are separate steps in the parent argument.

## Sources and internal derivation

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
  (1983), 367–464, proof of Theorem (2.7)(i)–(ii), printed pp. 391–392
  (one-based PDF pp. 26–27), especially display (6) and the paragraphs
  following it. Registered source: `jpss-1983-rankin-selberg`; retained
  file `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
  SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
  *Automorphic forms on GL(3) I*, Annals of Mathematics (2) **109**
  (1979), 169–212, §(2.2), definition of finite functions on printed
  p. 181 (one-based PDF p. 14). Registered source: `jps-1979-gl3-i`;
  retained file `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`;
  SHA-256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

These relevant pages were read directly and inspected visually. No
`notes/errata` directory was present in the workspace, project notes or
supplied Library when checked on 2026-10-29.

JPS defines a finite function on a locally compact abelian group through
continuity and finite-dimensional translation span. JPSS display (6)
reduces the analytic argument to products of one-variable integrals
against finite functions and Schwartz functions. The following paragraphs
assert convergence for large real part and rationality with denominator
control by the finite functions. Neither original separately states the
shell-series proposition above, the uniform recurrence or its precise
quantifier order. This module isolates an internal intermediate target
for a proof of the source-motivated Mellin assertion; it does not claim
to transcribe a numbered source theorem.

The intended derivation uses the already published
`FiniteTranslationOrbitStatement` proof for a recurrence and an
exponential orbit bound independent of `Φ`.
`SchwartzBruhatValuationBoundsStatement` supplies a lower support bound
and constancy of `Φ` near zero. Past that constancy threshold, integrating
the orbit recurrence over the integral units gives the recurrent tail.
Compactness of the integral units and the uniform exponential bound
control the integrals of the norm on positive shells by a convergent
geometric series for `B * ‖z‖ < 1`; only finitely many negative shells
can contribute. The published `ValuationShellIntegrationStatement` proof
then provides the actual integrability criterion and shell-sum identity.
These are intended proof ingredients, not hypotheses or a proof
implemented in this module. The parent still retains the complex-power
bridge, spectral substitution and denominator assembly.

Compilation and proposition inspection establish only that the closed
statement is well formed in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
