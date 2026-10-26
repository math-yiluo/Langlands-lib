# Uniform ramified Laurentness for scalar Mellin integrals

`Langlands.RankinSelberg.RamifiedFiniteFunctionMellinStatement.{uF}` is a
closed Prop-valued definition in
`Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinStatement`.
It states an analytic target and supplies no proof. It packages the scalar
Mellin and ramification arguments of JPSS (1983) into a uniform scalar
assertion with arbitrary positive integral spectral weights. This derived
formulation is not a separately numbered theorem in that source.

## Exact quantifier order

The proposition quantifies over every natural prime `p`, a witness
`Fact p.Prime`, every `F : PadicField.{uF} p`, and every supplied
`T : F.TopologicalData`. The field universe is arbitrary. It installs
`T.topology`, `T.valuativeRel`, `T.localField`, and the actual Borel
measurable structures and `BorelSpace` witnesses on both `F.Carrier` and
`F.Carrierˣ`. This covers finite extensions of `ℚ_p`; the original
nonarchimedean arguments have wider field scope.

Set locally `dmu = localMultiplicativeHaar F.Carrier`. For each function
`η : F.Carrierˣ → ℂ`, the only hypotheses are continuity and
finite-dimensionality over `ℂ` of

```text
Submodule.span ℂ
  (Set.range (fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a))).
```

The conjunction of these two hypotheses is the local `finiteFunction`
predicate. It uses left multiplicative translates, agreeing with the
finite-function definition of JPS (1979) on this abelian group.

After `η` and its hypotheses, the proposition asserts `∃ b : ℕ`.
Only then does it quantify over every
`α : HarmonicAnalysis.Quasicharacter F.Carrier` satisfying

```text
∃ u ∈ T.principalUnits b, α u ≠ 1,
```

every natural weight `m` with `0 < m`, and every
`Φ : HarmonicAnalysis.SchwartzBruhat F.Carrier`. Thus `b` can depend on
`p`, `F`, `T`, and `η`, and is independent of `α`, its unramified part,
`m`, and `Φ`. A quasicharacter is already a continuous multiplicative
map `F.Carrierˣ → ℂˣ`; continuity of `α` is built into its type.
No unitarity restriction is imposed. The weights include positive
multiples of `p`.

The filtration is the existing actual `T.principalUnits`, defined in
`Langlands.HarmonicAnalysis.Conductor` using `T.discreteValuation`.
Its zeroth level is the integral unit group; positive levels impose
congruence to one modulo the corresponding maximal-ideal power.
The condition on `α` requires nontriviality on this subgroup.
No supplied invariance level or decomposition of `η` is a hypothesis.

For each such `α`, `m`, and `Φ`, the local functions are exactly

```text
f(s,a) = Φ(↑a) * η(a) * (α(a) : ℂ)
           * (T.normalizedAbs ↑a : ℂ)^((m : ℂ) * s),
mellin(s) = ∫ a : F.Carrierˣ, f(s,a) ∂dmu.
```

The power is complex exponentiation. The measure is the actual normalized
multiplicative Haar measure, assigning mass one to the integral units by
`localMultiplicativeHaar_integerUnits`. The absolute value is the actual
`T.normalizedAbs`, and the spectral residue cardinality is
`q = T.residueCardinality`, rather than the base prime `p`.
The tests are all compactly supported locally constant functions on the
field, including functions nonzero at zero.

The conclusions are a conjunction:

1. There is `c : ℝ` such that for every `s : ℂ` with `c < s.re`,
   `MeasureTheory.Integrable (f s) dmu` holds.
2. There is `L : RankinSelberg.LaurentCoefficients` such that
   `HasRationalContinuation q mellin (laurentToRatFunc L)` holds.
   The existing relation requires agreement with rational evaluation at
   `spectralPoint q s = (q : ℂ)^(-s)` and nonvanishing of the reduced
   rational denominator throughout some right half-plane.

The convergence and continuation half-planes may have different bounds;
their intersection is a right half-plane where both assertions hold.
Actual integrability prevents Lean's totalized value for a divergent
Bochner integral from satisfying the intended analytic conclusion.
The second assertion adds Laurent polynomial continuation to ordinary
rationality. Negative powers of the spectral variable are permitted.
There is no assumption of prior convergence, rationality, L-factor
existence, or multiplicativity.

Every auxiliary predicate and function is a local let-binding. The sole
new public declaration is the proposition itself.

## Original sources and derived provenance

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
  (1983), 367–464: printed p. 392, displays (5)–(6) and the following
  convergence and denominator argument; printed p. 404, Proposition
  (2.13) and its proof. Registered source
  `jpss-1983-rankin-selberg`, retained at
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
  SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
  *Automorphic forms on GL(3) I*, Annals of Mathematics (2) **109**
  (1979), 169–212: §2, printed p. 181, the finite-function definition
  immediately before Proposition (2.2). Registered source
  `jps-1979-gl3-i`, retained at
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`;
  SHA-256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

The cited pages were read directly and visually, and both source hashes
were verified on 2026-10-26. No `notes/errata` directory was present in
the workspace, project notes, or supplied Library when checked that day;
no source-specific erratum was identified in the supplied literature
index. This records the bounded check of available project material.

On p. 392 JPSS separates finite functions and Schwartz tests into finite
tensor sums, reducing to scalar integrals with positive integral weights.
It then obtains convergence for large real part and rationality with
denominators controlled by the finite functions. On p. 404, the proof
of Proposition (2.13) uses a fixed finite set of scalar finite functions
and sufficiently ramified twists to make the corresponding integrals
Laurent polynomials in `q^(-s)`.

The present statement isolates that scalar mechanism and makes its
uniformity explicit. Mathematically, continuity and finite translation
span yield a finite-dimensional continuous translation representation.
Its restriction to the compact unit group has an open kernel, giving a
principal-unit level that fixes `η` under all translations. Establishing
this implication from the stated hypotheses remains part of a future
proof; it is not assumed as a certificate.

For a fixed Schwartz test, local constancy makes it constant sufficiently
near zero. A twist nontrivial on the fixed subgroup then forces the
integral on each sufficiently small valuation shell to vanish: translating
by a suitable subgroup element preserves `η`, the test, the absolute value,
and Haar measure, while multiplying the twist by a scalar different from
one. Compact support bounds the other end of the shell range. The
remaining finitely many shells give a Laurent polynomial. The neighborhood
where the test is constant may depend on `Φ`; the subgroup fixing `η`
and the ramification threshold do not. Unramified character factors are
trivial on principal units, explaining independence of the unramified part.

For the arbitrary positive weight `m`, rescaling the spectral parameter
from `s` to `m*s` preserves a right half-plane and replaces the formal
variable `X = q^(-s)` by `X^m`. This preserves Laurent polynomiality and
uses no condition that `m` be prime to `p`. Convergence still requires
the ordinary finite-function growth argument: shell cancellation alone
does not establish absolute integrability. These observations explain the
derived target and its remaining proof obligations; none is a formal proof
in this module. JPS Lemma (2.2.1) concerns the finite-function expansion
framework and is not cited as a proved Mellin theorem.

The finite-family torus extension, determinant-character power estimates,
Whittaker integral reductions, and the symmetric L-polynomial conclusion
belong to the parent work. In particular a later use with `α = χ^k`
requires its own conductor comparison; this scalar statement supplies
no such comparison. The ordinary rationality/common-denominator targets
`OneVariableMellinStatement` and `FiniteFunctionMellinStatement` remain
separate proof obligations.

Worker 611 authored this pair from Worker 394's scalar formulation and
source locators, using the published ordinary Mellin conventions.
