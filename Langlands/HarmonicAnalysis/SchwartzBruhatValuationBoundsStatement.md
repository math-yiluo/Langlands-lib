# Valuation cutoffs and uniform bounds for scalar Schwartz–Bruhat functions

`Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsStatement.{uF}` is a
Prop-valued definition. It states three elementary properties of one scalar
Schwartz–Bruhat function on a finite extension of `ℚ_p`: a uniform bound, a
lower order cutoff below which the function vanishes on units, and an upper
order cutoff above which it is constant on units. The module supplies no
proof of it; the separate published theorem
`Langlands.HarmonicAnalysis.schwartzBruhatValuationBounds` proves it (see
[Status](#status)). The proposition is a derived internal interface, not a
numbered result of the cited source.

## Exact scope

The proposition quantifies over every natural number `p` with an instance
`[Fact p.Prime]`, every `F : PadicField.{uF} p` and every supplied
`T : F.TopologicalData`. The field universe `uF` is arbitrary.

The only local instance is `letI := T.topology`. It is the topology in which
`HarmonicAnalysis.SchwartzBruhat F.Carrier` is formed, so local constancy and
compact support refer to the supplied topology and are not replaced by any
other topology. `T.valuativeRel` and `T.localField` are not installed: no
part of the statement needs them, and `T.ord` installs the supplied data
itself in its definition.

For every `Φ : HarmonicAnalysis.SchwartzBruhat F.Carrier` the proposition
asserts that there exist `L : ℤ`, `N : ℕ` and `C : ℝ` with

```text
L ≤ (N : ℤ)  ∧  0 < C  ∧
(∀ x : F.Carrier, ‖Φ x‖ ≤ C)  ∧
(∀ a : F.Carrierˣ, T.ord (a : F.Carrier) < L → Φ (a : F.Carrier) = 0)  ∧
(∀ a : F.Carrierˣ, (N : ℤ) ≤ T.ord (a : F.Carrier) → Φ (a : F.Carrier) = Φ 0).
```

Here `Φ x : ℂ` is the value given by the coercion of `SchwartzBruhat` to
functions, and `‖Φ x‖` is the complex norm.

- The bound clause is a non-strict inequality over every point of
  `F.Carrier`, including zero, with a strictly positive constant `C`.
- The vanishing clause uses the strict inequality `T.ord a < L`.
- The constancy clause uses the non-strict inequality `N ≤ T.ord a`, with the
  natural number `N` cast to `ℤ`. It compares with the value `Φ 0` at zero;
  it does not assert `Φ 0 = 0`.
- The thresholds are ordered by `L ≤ N`.

`L`, `N` and `C` are chosen after `Φ` and may depend on `p`, `F`, `T` and
`Φ`. They are existential witnesses inside the proposition; no auxiliary
function or definition is introduced.

The test functions range over the whole Schwartz–Bruhat space, including
functions that are nonzero at zero. The only properties of `Φ` available are
those bundled in `SchwartzBruhat`: local constancy and compact support. No
support bound, conductor, or unit invariance is assumed.

## Order direction and the zero convention

`T.ord` is the normalized additive order of the supplied valuation,
`T.ord x = -WithZero.log (T.discreteValuation x)`. A uniformizer has order
`1`, so a large order means a point close to zero. For nonzero `x`,
`T.normalizedAbs x = q ^ (-T.ord x)` with `q = T.residueCardinality > 1`.
The vanishing clause therefore concerns units of large normalized absolute
value, and the constancy clause units of small normalized absolute value.

The published convention is `T.ord 0 = 0`
(`Langlands.PadicField.TopologicalData.ord_zero`). This value does not record
that zero is closer to zero than every unit. Both order clauses therefore
range over units `a : F.Carrierˣ`, evaluated at `(a : F.Carrier)`, and say
nothing about the point zero through `T.ord`. The value at zero enters only
as the right-hand side `Φ 0` of the constancy clause and through the bound
clause.

## Original source and derivation

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
  (1983), 367–464, printed p. 392 (one-based PDF p. 27), display (6) and the
  following paragraphs. Registered source: `jpss-1983-rankin-selberg`;
  retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
  SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`
  (verified on 2026-10-27).

The scanned page was inspected visually. Display (6) is a product of
one-variable integrals of `Φ_i(a_i) η_i(a_i) |a_i^i|^s` against the
multiplicative measure, with `Φ_i ∈ S(F)` and finite functions `η_i`. The
source then says that this converges for `Re(s)` large and that, with
`X = q^(-s)`, each integral in (6) has the form `Q_i(X)(1 - α_i X)^(-k_i)`.
The standard argument for these two assertions relies on the facts formulated here: a Schwartz–Bruhat
function is bounded, vanishes where `|a|` is large and is constant where
`|a|` is small. The source states none of these as a separate result, and
this proposition is not quoted from it.

No errata for this article is registered in the project literature index,
and the supplied Library has no `notes/errata` directory (checked on
2026-10-27).

The consumer is the weighted one-variable Mellin statement
`Langlands.RankinSelberg.OneVariableMellinStatement`, whose integrand is
`Φ(↑a) * η(a) * (T.normalizedAbs ↑a : ℂ)^((m : ℂ) * s)` over
`a : F.Carrierˣ` with the same local `T.topology`. This proposition is a
separate prerequisite; the Mellin statement is unchanged.

## Proof route

A proof must establish the proposition from local constancy and compact
support in the supplied topology. Before the proof was written, the
following route was suggested: a continuous
compactly supported function is bounded; compact support bounds
`T.normalizedAbs` on the support and hence the order of units in the support
from below; local constancy at zero gives a small `T.normalizedAbs` ball
around zero on which `Φ` equals `Φ 0`, containing every unit of sufficiently
large order. Published results such as
`Langlands.PadicField.TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree`,
`topology_eq_canonicalNormTopology`, `normalizedAbs_balls_basis`,
`normalizedAbs_of_ne_zero` and `residueCardinality_gt_one` may help. This
route is not implemented or assumed in this module. The published proof
`schwartzBruhatValuationBounds` follows it, using these published results;
[SchwartzBruhatValuationBoundsProof](SchwartzBruhatValuationBoundsProof.md)
describes the implemented Lean argument.

Worker 231 authored this pair from the formulation specified by Worker 656's
task.

## Status

The proposition is proved by the theorem
`Langlands.HarmonicAnalysis.schwartzBruhatValuationBounds.{uF}` in
`Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof`. Its type is
exactly `SchwartzBruhatValuationBoundsStatement.{uF}`, with the same
arbitrary field universe and the supplied topology `T.topology`, and no added
hypothesis. The proof is artifact `c7adeca0-8f92-4b1c-bc39-b14c151c8cfd`
version 1. Its validation passed the Lake build and exact-target checks, an
independent review approved it, and it was published at Library commit
`4021bb1d1ec99e65990e08addda3ade7caa73058`. It proves only the bound and the
two order cutoffs stated here. It makes no measure, Mellin convergence or
rational-continuation assertion, and the one-variable Mellin statement remains
a separate proposition.
