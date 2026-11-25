# Proof of Bernstein–Zelevinsky (1977), Proposition 3.8

This module proves the published proposition
`Langlands.Derivative.MirabolicHighestDerivativePairingStatement` (module
`Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement`). The
proposition is Proposition 3.8 of Bernstein–Zelevinsky, *Induced
representations of reductive p-adic groups I* (BZ77), printed p. 453. The
statement pair is imported unchanged.

## Main declaration

```lean
theorem Langlands.Derivative.mirabolicHighestDerivativePairing.{uF, uV, uW}
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    MirabolicHighestDerivativePairingStatement.{uF, uV, uW} F T
```

Unapplied type:
`∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
Langlands.Derivative.MirabolicHighestDerivativePairingStatement.{uF, uV, uW} F T`.
The universe parameters `uF`, `uV`, `uW` are independent. There are no further
premises, instances or universe equalities. Axioms: `propext`,
`Classical.choice`, `Quot.sound` (the standard axioms only).

In words: let `ψ` be a unitary additive character, `A`, `B` smooth complex
representations of `P_(N+1) = mirabolic N`, and `0 < k ≤ N + 1`. Assume that the
order-`k` derivative of `A` is nonzero and every derivative of `A` of order
`j > k` is zero. Let `β` be a bilinear form on `A × B` with
`β(g v, g w) = |det g| β(v, w)` that is nondegenerate in `A`. Then there is an
invariant bilinear form on the order-`k` derivatives of `A` and `B` that is
nondegenerate in the first variable. The statement's Markdown explains why the
source's `Δ_P`-pairing is the Library covariance `+|det|`.

## Provenance

BZ77 proves Proposition 3.8 on printed p. 453 by induction on `k`, using the
exact sequence of Proposition 3.2(e), the lattice correspondence of Remark
3.3(a), and the pairing transfers of Propositions 3.4 and 3.7(a)(b)(c), all
through the plus functors `Φ⁺`, `Ψ⁺`. The implemented proof uses the same
induction on the number of `Φ⁻` steps, but no plus functor, exact sequence or
lattice correspondence:

* the `Φ⁻` step (the role of 3.7(b) with 3.3(a) and 3.4) is the unconditional
  `Langlands.Derivative.Mirabolic.phiMinus_nondegeneratePairing` of the companion
  module `MirabolicPhiMinusNondegeneratePairing`: every left-nondegenerate
  `|det|`-pairing of representations of `P_(m+2)` gives a left-nondegenerate
  `|det|`-pairing of their normalized `Φ⁻`;
* the `Ψ⁻` step (3.7(a) with 3.2(e) and 3.7(c)) is
  `psiMinus_nondegeneratePairing` of the companion module
  `MirabolicHighestDerivativeDescent`, applied when the radical acts trivially,
  which is `radical_acts_trivially_of_phiMinus` there (a direct proof of the
  case `Φ⁻ A = 0` of 3.2(e));
* the use of highestness (`Φ⁻ A = 0` at the last step) is the §3.5 detection
  `subsingleton_of_forall_mirabolicDerivative` of the companion module
  `MirabolicDerivativeVanishing`.

The source works with `Φ⁺Φ⁻A ⊂ A` and restricts the form to it; the Lean `Φ⁻`
step instead restricts the form to the radical relations `A(V)` and integrates
it along the radical, which avoids `Φ⁺` entirely: the route works with the
kernel of the `V`-coinvariant map directly.

## Implemented proof

Notation: `mirabolicDerivative T ψ n j = phiMinusIterate n j ⋙ psiMinus n`, a
functor from `P_(n+j+1)` to `GL_n`, and
`mirabolicDerivativeOfOrder T ψ N k hk = mirabolicRankCast (N = (N+1-k)+(k-1)) ⋙
mirabolicDerivative (N+1-k) (k-1)`. Since `phiMinusIterate` applies `Φ⁻` at the
largest rank first, `mirabolicDerivative n (j + 1)` is definitionally
`phiMinus (n + j) ⋙ mirabolicDerivative n j`.

* `highestDerivativePairing_core` (induction on `j`, for all `n`), with the
  `Φ⁻` step as a hypothesis `hΦ`. Highestness is carried in the form "every
  derivative `(n', i)` of `A`, at any splitting `n + j = n' + i` with `n' < n`,
  is zero".
  * `j = 0`: the radical acts trivially on `A`. For `n = 0` this is
    `radical_acts_trivially_zero` (the radical of `P_1` is trivial). For
    `n = m + 1`, `subsingleton_of_forall_mirabolicDerivative` applied to
    `Φ⁻_m A` shows `Φ⁻_m A = 0`: each derivative `(n', i)` of `Φ⁻_m A` is the
    derivative `(n', i + 1)` of `A`, and `n' ≤ m < n`. Then
    `radical_acts_trivially_of_phiMinus` gives triviality, and
    `psiMinus_nondegeneratePairing` gives the invariant left-nondegenerate form
    on `Ψ⁻ A × Ψ⁻ B`, which is `mirabolicDerivative n 0`.
  * `j + 1`: `hΦ (n + j)` turns `β` into a left-nondegenerate `|det|`-pairing
    of `Φ⁻ A`, `Φ⁻ B` on `P_(n+j+1)`. Highestness passes to `Φ⁻ A`
    (`subsingleton_rankCast_phiMinus`: a rank transport of `Φ⁻ X` is `Φ⁻` of the
    transported `X`, by `subst`). The induction hypothesis for `j` gives the
    form on `mirabolicDerivative n j (Φ⁻ A)`, which is
    `mirabolicDerivative n (j + 1) A` by `rfl`.
* `highestDerivativePairing_cast` moves the result along a rank transport
  `N = n + j`, by `subst`.
* `mirabolicHighestDerivativePairing_of_phiMinusStep` derives the statement from
  `hΦ` for every `ψ`: take `n = N + 1 - k`, `j = k - 1`. The highestness
  hypothesis of the statement, about orders `j' > k`, gives the vanishing of
  every derivative `(n', i)` with `n' < n` through
  `subsingleton_rankCast_mirabolicDerivative_congr` (order `i + 1 > k`).
* `Langlands.Derivative.mirabolicHighestDerivativePairing` discharges `hΦ` by
  `phiMinus_nondegeneratePairing`.

The hypothesis that the order-`k` derivative of `A` is nonzero is not used: the
conclusion holds without it. No highestness is needed for `B`.

## Normalization bridges

The proposition is stated with the Library's normalized minus functors
(`|det|^(-1/2)` twists) and the covariance `|det|` (via `T.determinantNorm`).
Every comparison is proved in Lean in the modules of this proof:

* `Ψ⁻` step (`MirabolicHighestDerivativeDescent`): `determinantNorm_levi`,
  `determinantNorm_radical`, and `half_power_mul_half_power_mul_self`, which
  shows that the two `|det|^(-1/2)` twists cancel the covariance `|det|`.
* `Φ⁻` step (`MirabolicPhiMinusNondegeneratePairing`):
  `determinantNorm_eq_determinantWeight` (Library `T.determinantNorm` versus the
  `determinantWeight` of `normalizedAbsoluteValue T` used by the published
  unnormalized transfer) and `phiMinusCharacter_mul_mul_determinantWeight`
  (the two `|det|^(-1/2)` twists turn the covariance `|det|^2` of the integrated
  form into `|det|`).

No plus functor is used, so no plus/minus or unnormalized/normalized functor
comparison arises. `Δ_P` versus `|det|` is settled by the statement's own
covariance convention; no Haar modulus comparison
(`Langlands.mirabolicRadicalHaarModulus`) is used.

## Auxiliary declarations

`subsingleton_rankCast_phiMinus`, `highestDerivativePairing_core`,
`highestDerivativePairing_cast`, `mirabolicHighestDerivativePairing_of_phiMinusStep`;
all are in namespace `Langlands.Derivative.Mirabolic`.

## Modules of this proof

The proof consists of four paired modules in
`Langlands/Representation/Derivative/`:

* `MirabolicDerivativeVanishing`: the §3.5 detection and the
  published `MirabolicDerivativeDetection` in the form
  `Langlands.Derivative.Mirabolic.derivativeDetection`.
* `MirabolicHighestDerivativeDescent`: radical triviality from
  `Φ⁻ = 0` and the `Ψ⁻` descent of pairings.
* `MirabolicPhiMinusNondegeneratePairing`: the `Φ⁻` step.
* `MirabolicHighestDerivativePairingProof`: this assembly.

Each module's Markdown states its lemmas, describes their proofs and audits
its own import closure.

## Imports and independence audit

Direct imports: `MirabolicHighestDerivativeDescent`,
`MirabolicPhiMinusNondegeneratePairing` and the statement module
`MirabolicHighestDerivativePairingStatement`. The transitive `Langlands` import
closure of this module has 110 modules: the 4 modules of this proof and 106
public Library modules. Every public Lean/Markdown pair in it is byte-identical
to the Library at `6789e5106aba61566887427750f5444a494d5879`.

The 106 public modules are:

* the 73 of `MirabolicDerivativeVanishing` (groups, local fields and their
  normalization, harmonic-analysis conductors, smooth representations and
  twists, localization and character averaging, compact orbit means, matrix
  coefficients, Whittaker characters, the elementary Rankin–Selberg lattice and
  quotient-integral lemmas used by `MinusVanishing`, `MinusVanishing`,
  `MirabolicMinus`, `Iteration`, `Homogeneity`, `MirabolicLatticeBox`, the
  detection statement);
* `Filtration.InvariantBilinear`, `Filtration.Definitions`,
  `Filtration.ObjectDefinitions` (from `MirabolicHighestDerivativeDescent`);
* the statement module `MirabolicHighestDerivativePairingStatement`;
* 29 modules reached through `MirabolicPhiMinusNondegeneratePairing`: the
  published `MirabolicMinusPairingTransferProof` and its statement,
  `Group.GL.MirabolicProjection`, `Group.GL.IntegralSubgroup`, `Group.GL.Maps`,
  `HarmonicAnalysis.CharacterTransport`,
  `HarmonicAnalysis.PadicRectangularHaarScalingProof`,
  `HarmonicAnalysis.RowSchwartzAction`, `HarmonicAnalysis.RowTestSmoothProof`
  and its statement, `LocalFactor.Euler` and `LocalFactor.Euler.Definitions`,
  `Representation.Conductor.Congruence`, `Filtration.InvariantBilinearBounds`,
  `Hecke.TestFunction`, the Rankin–Selberg modules `AnalyticStatement`,
  `EqualRankFrobeniusProof` and its statement, `EqualRankTrilinearAssembly`,
  `EqualRankTrilinearReduction`, `EqualRankTrilinearUniquenessStatement`,
  `LocalFactor`, `Measures`, `RationalContinuation`, `RationalZeta`,
  `TwistInvariance`, and `Whittaker.AlgebraicTwist`, `Whittaker.DualTransform`,
  `Whittaker.Twist`.

Mathematical proof dependencies of the main theorem: the definitions of the
minus functors, derivatives, rank transports and invariant-form spaces; the
published `MinusVanishing` lemmas (one-step detection, coordinate
characters, Levi transport, radical boxes, finite Fourier inversion) and
`Jacquet.CharacterAveraging`; the published unnormalized pairing
transfer `MirabolicMinusPairingTransferProof` (radical integral, descent to
coinvariants, Haar change of variables, finite Fourier nonvanishing), whose
lower inputs include `EqualRankFrobenius.exists_lastRow_eq` and elementary
Haar-scaling and row-test lemmas; `Compact.ProjectionProof`; and the elementary
determinant bridges listed above. The Rankin–Selberg statement modules in the
closure (`AnalyticStatement`, `EqualRankTrilinearUniquenessStatement`,
`EqualRankFrobeniusStatement`) are imported only as definitions of
propositions; none is assumed. No minus-functor exactness (the published
`MinusExactnessStatement` is neither imported nor used), no plus functor, no
`Φ⁺Φ⁻`/`Ψ⁺Ψ⁻` exact sequence, no Haar modulus comparison and no consumer
result is used. The only derivative results used are published
proofs (`MinusVanishing`, `MirabolicMinusPairingTransferProof`) and the
results proved in the four modules of this proof.

The proof is independent of the following results, without weakening. Neither
these four modules nor their import closure use: the nonadjacent product
consumer `TwoSupercuspidalNonadjacentProductIrreducible` or its
conclusion; `TwoSupercuspidalProductStructure`; the special-head/reverse-socle,
segment-socle/reverse-head, analytic segment classification, forward special
square-integrability (`SegmentSpecialEssentialSquareIntegrability`),
multisegment special-head exhaustion, ordered strong-head existence, quotient
coverage, ordered conversion, tempered uniqueness,
`SquareIntegrableLanglandsClassification`, square-integrable and regular
exhaustion, special-head product irreducibility,
`GenericSegmentProductUniqueness`, `OrderedMultisegmentSocleExistence`,
`MultisegmentSocleExhaustion`, `SegmentSocleProductIrreducibility`, adjacent
socle commutation, `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
`SegmentSocleJacquetFormula` or `SegmentSpecialJacquetExponentNormFormula`
statements, conclusions, proofs or consequences; Ze80's
segment derivative formulas (§3.5, §9.6); a segment product irreducibility
criterion (Ze80 4.2, 9.7); an analytic or square-integrability result
(Ze80 9.3); or any classification or exhaustion theorem. A text scan of all 110
Lean files of the closure finds none of these declaration names. In the
Markdown files the only hits are the independence paragraphs of `Iteration.md`
and `MirabolicMinus.md`, and of the Markdown of these four modules, which state that
those names are not used.
