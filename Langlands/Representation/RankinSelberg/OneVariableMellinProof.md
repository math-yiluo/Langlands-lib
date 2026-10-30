# Weighted one-variable Mellin analysis: proof

`Langlands.RankinSelberg.oneVariableMellin.{uF}` proves exactly
`Langlands.RankinSelberg.OneVariableMellinStatement.{uF}`. The field universe
is arbitrary. The statement and its imported pairs are unchanged. Worker 656
assembled the proof; the two private spectral proofs identified below
are adapted from Worker 235's published work.

The theorem covers every prime, supplied p-adic field and topological data,
positive natural weight `m`, and continuous function `η` with finite-dimensional
complex left-translation span. It uses the full Schwartz–Bruhat space,
the actual normalized multiplicative Haar measure, the supplied normalized
absolute value, and the actual Bochner integral. It proves integrability on
a right half-plane, rational continuation in the spectral variable
`X = q^(-s)`, and one nonzero Laurent denominator for every continuation of
every test, where `q` is the residue cardinality of the supplied field.

## Published inputs

The proof imports and applies these theorems by Lean name:

- `Langlands.RankinSelberg.finiteFunctionShellSeries` from
  `Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesProof`
  (Worker 277) supplies an order-one uniformizer `π`, a complex recurrence
  `E`, and a real growth base `B ≥ 1`, all chosen before the test function.
  For each test `Φ`, its coefficients are the actual set integrals
  `c(n) = ∫ u in K, Φ(↑(π^n*u)) * η(π^n*u) ∂dA` over integral units.
  It supplies cutoffs `L : ℤ`, `N : ℕ`, with `L ≤ N`, vanishing below `L`
  and the `E`-recurrent tail `j ↦ c(j+N)`. For nonzero `w` with
  `B*‖w‖ < 1`, it proves integrability of the actual integrand
  `a ↦ Φ(↑a)*η(a)*w^(ord(↑a))`, bilateral summability, and equality of its
  integral with `∑' n : ℤ, c(n)*w^n`.
- `Langlands.Analysis.eventuallyRecurrentLaurentSeriesStatement_proof`
  from `Langlands.Analysis.EventuallyRecurrentLaurentSeriesProof`
  (Worker 740) supplies a positive radius `ρ` depending only on `E`.
  For each positive `m`, the nonzero Laurent denominator is
  `D = (Q.comp (Polynomial.X ^ m)).toLaurent`, where
  `Q = 1 - ∑ i : Fin E.order, C(E.coeffs i)*X^(E.order-i.val)`.
  For every coefficient sequence with the stated cutoffs and recurrence,
  it constructs `R` and `P` before the evaluation point, with
  `laurentToRatFunc P = laurentToRatFunc D * R`. For nonzero `z` with
  `‖z^m‖ < ρ`, it proves summability, nonvanishing of the reduced denominator
  of `R` at `z`, and equality of the bilateral sum to `RatFunc.eval id z R`.

The shell proof in turn uses the published translation-orbit, Schwartz
valuation-cutoff and valuation-shell integration results. The Laurent proof
uses the published natural recurrence generating-series result. Their proof
text is not copied here; their existing hypotheses are discharged by the
unchanged parent hypotheses and the actual shell coefficients.

## Complex powers and the half-plane

The private lemmas `mellin_natCast_zpow_cpow_eq` and
`mellin_exists_re_threshold` adapt Worker 235's private
`natCast_zpow_cpow_eq` and `exists_re_threshold` in
`Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinProof`.
They use elementary complex and real power identities; no ramified Mellin
conclusion is used.

Nonvanishing uses the existing public theorem
`Langlands.RankinSelberg.spectralPoint_ne_zero` from
`Langlands.Representation.RankinSelberg.EpsilonFactor`. Its statement and
proof coincide with the private helper in the reviewed contribution, so the
integrated module reuses it.

Positivity of `q` gives argument zero for its complex image. The integer
complex-power identities therefore give

```text
((q^(-k) : ℝ) : ℂ)^((m : ℂ)*s) = (spectralPoint q s ^ m)^k.
```

The spectral point is nonzero. Its norm is `q^(-s.re)`. For any `ρ > 0`,
the threshold `-log(min ρ 1)/log q` makes this norm less than `min ρ 1`;
raising to positive `m` cannot increase a nonnegative number at most one.
Here `q > 1` ensures `log q > 0`.

`mellin_normalizedAbs_cpow` substitutes the actual normalization formula
`T.normalizedAbs a = q^(-T.ord a)` for a unit `a`. The joint-threshold
lemma applies the preceding bound with `min (1/B) ρ`, using `B ≥ 1`, to
choose one real `c0` such that whenever `c0 < s.re`,

```text
B * ‖spectralPoint q s ^ m‖ < 1,
    ‖spectralPoint q s ^ m‖ < ρ.
```

This threshold is chosen before all tests.

## Assembly and the uniform denominator

The main proof installs exactly the topology, valuation, local-field and
Borel instances required by the target. It introduces the target's local
measure, integrand, Mellin integral and rational-values set without replacing
them. It chooses `π,E,B`, then `ρ` and `D`, then the joint half-plane.

For each `Φ`, the local assertion `htest` takes the actual coefficients and
cutoffs from the shell theorem and applies the Laurent theorem to that same
sequence. At `z = spectralPoint q s`, nonvanishing of `z` gives nonvanishing
of `z^m`. Rewriting the weighted absolute value by the proved power identity
makes the shell integrand definitionally the target integrand. The first
bound proves actual integrability. The shell integral equals the bilateral
sum, and the second bound identifies that sum with the rational evaluation.
The Laurent theorem also gives the required reduced-denominator guard.
These facts produce `HasRationalContinuation` and a Laurent clearing witness
for this test on the common half-plane.

The first two target conclusions follow from `htest`. For the third, `D`
was fixed using only `E,m`, before any `Φ` or rational witness. Given any
member `R` of the target's rational-values set, take its test `Φ` and the
constructed continuation `S` for that test. The unchanged
`HasRationalContinuation.unique`, using `q > 1`, identifies `R` with `S`.
The already constructed clearing identity for `S` consequently clears `R`.
Thus the same nonzero `D` works for all tests and all their continuations.

No restriction on `Φ(0)`, sign of the integer lower cutoff, recurrence order,
or dimension of the translation span is introduced. Those boundary cases
are covered by the unrestricted published inputs. Positivity of `m` is
exactly the target hypothesis.

## Original sources and provenance

This is a derived proof of the existing one-variable interface. Its route
uses recurrences and generating series rather than decomposing `η` into
character-polynomial functions. The original-source motivation and exact
scope are recorded in the unchanged statement Markdown:

- Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions*
  (1983), proof of Theorem (2.7)(i)–(ii), printed pp.391–392,
  one-based PDF pp.26–27, especially display (6) and the subsequent
  convergence, rationality and common-denominator discussion. Registered
  source `jpss-1983-rankin-selberg`, retained SHA-256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- Jacquet, Piatetski-Shapiro and Shalika, *Automorphic Forms on GL(3) I*
  (1979), §2, printed pp.180–182, one-based PDF pp.13–15, with the
  finite-function definition on p.181. Registered source `jps-1979-gl3-i`,
  retained SHA-256
  `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

These passages were read directly in developing this task; JPSS pp.391–392
and the JPS definition on p.181 were also inspected visually. The arbitrary
positive weight is the existing statement's derived extension of the JPSS
weights, realized here by substitution `X^m`. This module establishes only
the scalar statement. The multivariable tensor and Fubini assembly remains
a separate theorem.
