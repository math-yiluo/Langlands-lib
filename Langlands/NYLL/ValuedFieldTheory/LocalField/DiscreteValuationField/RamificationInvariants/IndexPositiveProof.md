# M343.003: positivity of the canonical ramification index

The theorem
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_pos`
proves exactly the published proposition
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_posStatement`.
That proposition is in the module
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants.IndexStatements`.
The proof module imports only that statement module. It edits neither the statement
nor anything the statement imports.

## Statement proved

The theorem has the target's complete outer telescope, in the target's order:

```lean
{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
[base.valuation.HasExtension target.valuation]
[Module.IsTorsionFree base.valuationSubring target.valuationSubring]
```

Its result type is `ramificationIndex_posStatement base target`. This unfolds to

```lean
0 < Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal
```

The four universes `u v w x` remain independent. The field types are implicit,
the two `CompleteDVF` packages are explicit, and all other hypotheses are instance
binders. There are no further element or natural-number binders. The proof adds
no finite-dimensionality, `Module.Finite` or scalar-tower hypothesis.
A development check assigned the unapplied constant `@ramificationIndex_pos` to
this complete `∀`-telescope ending in the statement application, and it compiled
without errors.

The objects are the published ones:

- `base.valuationSubring` and `target.valuationSubring` are the chosen valuation
  subrings of the `CompleteDVF` packages. They are read through
  `CompleteDVF.toHenselianDVF`.
- `base.maximalIdeal` and `target.maximalIdeal` are their canonical local-ring
  maximal ideals.
- The algebra between them is Mathlib's
  `Valuation.HasExtension.instAlgebra_valuationSubring`. It comes from the
  supplied `HasExtension` instance.

The source M108.003 index wrapper and the M108.005 algebra map are represented by
their exact Mathlib bodies, `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal`
and `algebraMap base.valuationSubring target.valuationSubring`. These are already
present in the published statement.

## Implemented proof

The proof is two tactic steps.

1. `apply Nat.pos_of_ne_zero` reduces the goal `0 < ramificationIdx' …` to
   `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal ≠ 0`.
2. The goal is then closed by Mathlib's
   `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`.
   The proof gives `P := target.maximalIdeal` and
   `hp := IsDiscreteValuationRing.not_a_field base.valuationSubring`,
   which says `base.maximalIdeal ≠ ⊥`.

The Mathlib lemma is stated for `R → S` with `S` a Dedekind domain, `R` a domain
and `S` torsion-free over `R`. It also needs a prime `P` of `S` lying over a
nonzero ideal `p` of `R`. Elaboration fills its remaining arguments as follows.
This was confirmed by printing the elaborated proof term with explicit instances.

| Lemma argument | Supplied by |
| --- | --- |
| `IsDedekindDomain target.valuationSubring` | `IsPrincipalIdealRing.isDedekindDomain`, from `IsDiscreteValuationRing.toIsPrincipalIdealRing` and Mathlib's `Valuation.valuationSubring_isDiscreteValuationRing`. That instance uses the rank-one discreteness stored in the published `CompleteDVF.instCompleteDiscrete` (`Valuation.IsCompleteDiscrete.isRankOneDiscrete`). |
| `IsDomain base.valuationSubring` | `ValuationSubring.instIsDomainSubtypeMem` |
| `Module.IsTorsionFree base.valuationSubring target.valuationSubring` | the theorem's own instance hypothesis, the last binder of the statement |
| `target.maximalIdeal.IsPrime` | `Ideal.IsMaximal.isPrime'` applied to `IsLocalRing.maximalIdeal.isMaximal` |
| `target.maximalIdeal.LiesOver base.maximalIdeal` | Mathlib's instance `Valuation.HasExtension.instLiesOverSubtypeMemValuationSubringValuationSubringMaximalIdeal` (`Mathlib/RingTheory/Valuation/Extension.lean`). It comes from `maximalIdeal_comap_algebraMap_eq_maximalIdeal` for the canonical valuation-subring algebra. |
| `p ≠ ⊥` with `p = base.maximalIdeal` | `IsDiscreteValuationRing.not_a_field base.valuationSubring` |

The torsion-free hypothesis is therefore used. The `HasExtension` hypothesis
supplies both the algebra and the lying-over instance. The development check
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source correspondence

The source result is `ramificationIndex_pos` in the namespace
`LocalFieldTheory.DiscreteValuationField.ValuedExtension`. It is at lines 65–70 of
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationInvariants.lean`
(SHA-256 `e8f6193618b69865b663a601b6063cbab7231d8ce39259501305d26ffc262e4d`),
NYLL commit `fbd320cd8b1b06487c58227e92eb135794267709`. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The target's paired Markdown gives the complete statement correspondence.

The source proof is `Nat.pos_of_ne_zero (ramificationIndex_ne_zero base target)`.
Its M343.002 `ramificationIndex_ne_zero` (lines 54–59) delegates to
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_ne_zero`.
That theorem is at lines 758–767 of
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteExtension/Degree.lean`
(SHA-256 `af4de3740b8a9a4e4717464fe46b5d69a27d7c346aaf327678105a54d00de28d`).
It applies the same Mathlib lemma
`Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`, with a local
`LiesOver` proof from NYLL's `maximalIdeal_liesOver` and `base.maximalIdeal_ne_bot`.

The adapted proof keeps this route but inlines it. It uses Mathlib's
`LiesOver` instance in place of NYLL's `maximalIdeal_liesOver`. It uses
`IsDiscreteValuationRing.not_a_field` in place of `base.maximalIdeal_ne_bot`.
It needs no unpublished NYLL theorem, and in particular no proof of the
M343.002 statement `ramificationIndex_ne_zeroStatement`. Every dependency is in
the current Library or the pinned Mathlib
(`5ed2965256430c3649e86755f9576b54eca72435`, Lean v4.34.0).

## Attribution and modifications

The paired Lean file retains the original Apache-2.0 copyright and author header
(copyright 2026 Naganori Yamaguchi, `https://github.com/n-yamaguchi-0729`; authors
Naganori Yamaguchi, assisted by OpenAI Codex). The carried
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged.

The modifications from the source are:

- the `Langlands.NYLL` namespace prefix;
- the explicit published `Statement` result type;
- the single focused import of the statement module;
- the inlined M108.003 and M108.005 wrapper bodies already fixed by the statement;
- replacing the call to the M343.002 theorem with the direct Mathlib argument described above;
- added docstrings and this documentation.

Worker 308 designed the proof and the first version of this documentation in this
task's shared draft revision 1. Worker 426 checked the design against the
published statement and the original sources. Worker 426 also added the docstrings,
expanded this explanation and prepared the submission. The Lean proof body is
unchanged from Worker 308's design.
