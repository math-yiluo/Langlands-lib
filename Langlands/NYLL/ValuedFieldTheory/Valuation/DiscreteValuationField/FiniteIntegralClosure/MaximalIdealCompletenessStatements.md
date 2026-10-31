# Positive-power and integral-closure maximal-ideal completeness targets

This module contains exactly two closed Prop-valued definitions, stating NYLL
M105.013 and M245.014 without proofs. The entry module is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdealCompletenessStatements`.
Each complete unapplied declaration has type `Prop`; its only declaration
parameters are independent universe levels. Every mathematical parameter,
structure and hypothesis is quantified inside the proposition.

## Positive-power completeness

The first declaration is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.IsAdicCompleteOfIsAdicCompletePowStatement.{u, v}`.
Its complete body is:

```lean
∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
  (I : Ideal R) {n : ℕ} (hn : 0 < n) [IsAdicComplete (I ^ n) M],
  IsAdicComplete I M
```

For any commutative ring `R`, additive commutative group `M` with the supplied
`R`-module structure, ideal `I`, and strictly positive natural number `n`,
completeness of `M` for `I ^ n` implies completeness for `I`. The same ring,
module action and ideal occur on both sides. The ring universe `u` and module
universe `v` are independent. The exponent is implicit, its positivity proof
is explicit, and the power-completeness hypothesis is instance-implicit, as in
the source.

`IsAdicComplete` is Mathlib's actual algebraic ideal-adic completeness class
from `Mathlib.RingTheory.AdicCompletion.Basic`. It comprises
`IsHausdorff I M`, expressing separation by the powers `I ^ k • ⊤`, and
`IsPrecomplete I M`, expressing convergence of compatible Cauchy sequences
modulo those submodules. No topology is supplied separately. There is no
Noetherianity, finite-generation, algebra, nontriviality, field or valuation
hypothesis on `R` or `M`.

The source theorem combines the Hausdorff and precomplete positive-power
helpers at `AdicPower.lean` lines 204–243. The former tests the powers at
multiples of `n`; the latter takes a limit of the subsequence indexed by
`n * k` and uses `0 < n` to compare it with the original sequence.
These are steps in the original proof, not extra hypotheses or separate
targets here. The strict positivity hypothesis is retained in the statement.

## Completeness for the integral closure's own maximal ideal

The second declaration is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.IntegralClosureMaximalIdealIsAdicCompleteOfFiniteSeparableStatement.{u, v, w}`.
Its complete body, using the enclosing published namespace, is:

```lean
∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
  IsAdicComplete
    (CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base)
    (integralClosure base.valuation.valuationSubring L)
```

For any fields `K` and `L`, supplied `K`-algebra structure on `L`, finite
dimension and separability, and supplied complete discrete valuation bundle
`base` on `K`, the actual integral closure of the supplied valuation subring in
`L` is complete for its own canonical maximal ideal. The universes are
independent: `K : Type u`, the value group stored in `base` is in `Type v`,
and `L : Type w`. The proposition includes the trivial extension `L = K`.
There is no proper-extension hypothesis.

Write `A := base.valuation.valuationSubring` and `B := integralClosure A L`.
The bundle
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K`
stores the supplied valuation, its value group, rank-one discreteness and
maximal-ideal adic completeness of `A`. The ring `A` is the actual valuation
subring of `K`. The ring `B` is Mathlib's integral-closure subalgebra of `L`,
using the inclusion `A → K` followed by the supplied `algebraMap K L`.
The conclusion uses `B` with its own ring-module structure.

The ideal is exactly the published definition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.CanonicalIntegralClosure.maximalIdeal`.
That definition locally installs the witness from the published theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base`
and returns `IsLocalRing.maximalIdeal B`. Thus it is the canonical ideal of
non-units of this actual integral closure. The statement takes no additional
local-ring witness, chosen extension valuation, selected integral closure,
chosen maximal ideal, equality of ideals or completeness premise.

The conclusion is completeness for this upstairs maximal ideal. In the source
proof, M245.013 writes the image of the base maximal ideal as a positive power
of the upstairs ideal, M245.003 gives completeness for the image ideal, and
M105.013 supplies the final reduction. These are the original proof's
dependencies, not premises of the present proposition. This module does not
implement that proof.

## Source correspondence and grouped layout

The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The two source declarations map as
follows:

| Source declaration | Source locator | Adapted declaration |
| --- | --- | --- |
| `ValuationTheory.DiscreteValuationField.isAdicComplete_of_isAdicComplete_pow` | `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AdicPower.lean`, lines 247–253; ambient variables lines 22–24 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.IsAdicCompleteOfIsAdicCompletePowStatement` |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_maximalIdeal_isAdicComplete_of_finite_separable` | `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`, lines 428–457; universe line 23 and ambient variables lines 30–31 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.IntegralClosureMaximalIdealIsAdicCompleteOfFiniteSeparableStatement` |

Worker 384 read `AdicPower.lean` lines 1–27 and 203–253 and
`FiniteIntegralClosure.lean` lines 1–64 and 428–457, including both source
proofs and the two positive-power helpers. The module layout is a focused
statement extraction grouping the small generic prerequisite with its direct
consumer: the source M245.014 proof ends by applying M105.013. It does not
port the surrounding source modules.

The adaptations are:

- Add the `Langlands.NYLL` namespace prefix and use the two task-specified
  statement names in place of the source theorem names.
- Replace each theorem with a `def ... : Prop`, quantifying all mathematical
  parameters inside its body. Make the source's independent universe levels
  explicit; give the generic ring and module universes the names `u` and `v`.
  The source's unused ambient module `N` does not enter M105.013.
- Expand the source abbreviation `base.valuationSubring` to
  `base.valuation.valuationSubring`. The published
  `CompleteDVF.valuationSubring` in `Complete.Projections` follows the
  forgetful projections with the same valuation and reduces to this actual
  subring. No subring or integral closure is replaced.
- Map the source
  `ValuationTheory.DiscreteValuationField.ValuedExtension.CanonicalIntegralClosure.maximalIdeal`
  to the published definition with the `Langlands.NYLL` prefix, preserving its
  localness witness from the finite-separable localness theorem.
- Replace the source imports by the published
  `FiniteIntegralClosure.MaximalIdeal` module and Mathlib's
  `RingTheory.AdicCompletion.Basic`. Omit the original theorem proofs.

These statements add no global instances or axioms. No later extension
valuation, host comparison, inertia or reciprocity assertion is made. Exact
proof work against either target follows independent acceptance and
publication of both targets.

## Attribution and source records

Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable pinned source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The verified source SHA256 hashes are:

| File | SHA256 |
| --- | --- |
| `AdicPower.lean` | `df1f92c6b85a87ad4a27c319302f267a717b7f82c1cce10167c56b1c4793232d` |
| `FiniteIntegralClosure.lean` | `43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094` |

The registered attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No source-specific entry for these two files was found in upstream NOTICE,
and no applicable project erratum was found.

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex);
Apache-2.0. The unchanged
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany the adaptation.
Worker 384 wrote the statement extraction and this Markdown on
30 October 2026 and recorded the modifications in the Lean header. Worker 106
provided routing and the focused contract, with no implementation draft.
Importing the published definitions and the localness theorem is reuse by
Lean name, not reuse of another worker's unpublished adapted draft.

The approved checking environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The original used
Lean 4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Compilation and inspection of these statement definitions do not prove them;
independent semantic review and publication are separate requirements.
