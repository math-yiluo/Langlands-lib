# Square-integrable equal-rank convergence and holomorphy

Author: Worker 113.

`Langlands.RankinSelberg.SquareIntegrableEqualRankAnalyticStatement.{uF,uV,uW}`
is a proposition definition, not a theorem or an axiom. It states the equal-rank
analytic conclusion of JPSS Section 8.3 for the Library's actual integral. The
absolute convergence and holomorphy assertions remain proof obligations.

## Statement and existing definitions

For every prime `p`, every `F : PadicField.{uF} p`, every compatible local-field
structure `T : F.TopologicalData`, and every positive rank `n + 1`, the statement
quantifies over a `UnitaryAdditiveCharacter F.Carrier`. This structure includes
continuity, nontriviality and unit modulus. The topology and valuation are those
of `T`; no equality with the canonical topological data is required. In
particular, `T = F.canonicalTopologicalData` is an allowed specialization.

The general linear group, its upper-unipotent subgroup and the actual left
quotient `LeftUnipotentQuotient n F.Carrier` carry their Borel measurable
structures. The statement quantifies over an
`IsMulRightInvariant (unipotentHaar F.Carrier n)` instance and every measure `μ`
on that quotient satisfying `QuotientIntegration.IsCompatible` with
`generalLinearHaar F.Carrier n` and `unipotentHaar F.Carrier n`. Right invariance
here is an instance on the subgroup Haar measure, as required by the existing
compatibility predicate. Compatibility itself supplies the quotient measure's
nonzero, regular and right-translation-invariant properties and the Weil
integration formula. The two Haar measures retain their published normalization
on integral points. No new measure or measure-existence assumption is introduced.

The two complex representation carriers `V : Type uV` and `W : Type uW` have
independent universes. For representations `π` and `σ` of `GL_(n+1)(F)`, the
hypotheses are `Representation.IsIrreducible π`, `T.IsSquareIntegrable π`, and
the corresponding two hypotheses for `σ`. The square-integrability predicate
is exactly the analytic definition from `Classification.Tempered`: it uses
admissibility, a unitary central character, and square-integrability of the
absolute values of smooth-dual matrix coefficients on the actual central
quotient for every Borel Haar measure. The central quotient is distinct from
the left-unipotent quotient used in the JPSS integral. No exponent criterion,
alternative square-integrability definition, convergence, holomorphy or local
factor is assumed.

For every `ℓ : glFunctionals ψ n π` and
`ℓ' : glInverseFunctionals ψ n σ`, every vector `f` and `f'` in their actual
`coefficientModel` images, and every
`Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)`, the conclusion is the conjunction
of:

- `EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s`
  for every `s : ℂ` with `0 < s.re`;
- `DifferentiableOn ℂ` of the function
  `equalRankModelIntegral ψ (normalizedAbsoluteValue T) μ π σ ℓ ℓ' f f' Φ`
  on `{s : ℂ | 0 < s.re}`.

The first clause is Bochner integrability of the descended complex integrand,
so it asserts absolute convergence separately from the total integral's value.
The second clause concerns that same actual integral as a function of `s`.
The integrand before descent is

\[
 f(g)f'(g)\Phi(e_{n+1}g)|\det g|^s.
\]

Here the opposite Whittaker characters cancel, and the last row and determinant
are invariant under left upper-unipotent multiplication. The weight uses the
existing `normalizedAbsoluteValue T`, with uniformizer value `q⁻¹`, not a
base-extending absolute value or an unequal-rank shift.

Nonzero-functional hypotheses are unnecessary. For a nonzero functional, the
irreducible representation's coefficient image is its Whittaker model, by the
existing coefficient-map construction and its injectivity for irreducible
representations. If either functional is zero, its coefficient map is zero
and its image consists only of the zero function. The integrand and integral
then vanish identically, giving both conclusions. The statement does not assert
existence of a nonzero functional or select one.

## Original source and provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105** (1983),
367–464, Section 8.3, printed pages 448–451; registered source
`jpss-1983-rankin-selberg`. The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original pages were read visually. In this exact file, printed pages
448–451 are zero-based PDF indices 82–85 (one-based pages 83–86).
No source-specific erratum file was present in the checked project, Library
or literature `notes/errata`/`errata` locations.

The proposition on printed page 448 states absolute convergence for
`Re(s) > 0`, uniformly on compact subsets of that half-plane, for the equal-rank
integrals `Ψ(s,W,W',Φ)` when the representations are square-integrable.
The unequal-rank assertion in the same proposition is outside this module's
scope. Printed page 449 gives the integration formula (1), the square norm
estimate (2), and the equal-rank decomposition (3). Its estimate (4) splits the
determinant range into values at most one and at least one, using square norms
for the first part and gauge bounds for the second. Printed page 450 continues
the estimates and begins the unequal-rank case. Printed page 451 finishes that
case and explicitly leaves the proof of normal convergence to the reader.
Thus the source asserts local uniform convergence but does not supply a complete
normal-convergence proof there.

The `DifferentiableOn ℂ` clause is a derived complex-analysis formulation, not
verbatim wording of the proposition. For each fixed quotient point, the spectral
weight has the form `exp(s * log a)` for a positive determinant norm `a`, hence
is entire. On a compact subset of the half-plane, choose real numbers
`0 < α < β` bounding all real parts. The absolute value of `a^s` is bounded by
`a^α + a^β`: split into `a ≤ 1` and `a ≥ 1`. Absolute convergence at `α` and `β`
therefore gives an integrable bound for the absolute integrands, locally
uniformly in `s`. The usual holomorphy theorem for dominated parameter integrals
(or compact truncations and locally uniform convergence of holomorphic
functions) then yields holomorphy of the actual integral. Since the half-plane
is open, this is expressed by `DifferentiableOn ℂ` on that set. This is the
provenance of the additional formulation; the present module does not implement
that argument in Lean or claim that JPSS wrote out the omitted normal-convergence
step.

The source works over non-Archimedean local fields. This statement restricts it
to the existing `PadicField` interface, retains all positive ranks including
rank one, and uses the supplied compatible quotient measures and the existing
coefficient images. It adds no rational continuation, normalized-generator
existence or pole-free local-factor conclusion. Those remain separate
statements and proof tasks.
