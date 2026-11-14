# M343.002: ramificationIndex_ne_zero

The theorem
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_ne_zero`
proves exactly the published target
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_ne_zeroStatement`
from the Library module
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants.IndexStatements`.
Its result type is the application `ramificationIndex_ne_zeroStatement base target`.
This module imports only that statement module and does not edit the statement
or anything it imports.

## Statement proved

The four universes `u v w x` remain independent. The complete telescope, in
source order and with the source binder kinds, is:

```lean
{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
[base.valuation.HasExtension target.valuation]
[Module.IsTorsionFree base.valuationSubring target.valuationSubring]
```

Here `CompleteDVF` is the published
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF`.
The target has no further element or natural-number binders, and no
finite-dimensionality, finite-module or scalar-tower hypothesis is introduced.
The statement body is

```lean
Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal ≠ 0
```

for the chosen valuation subrings and their canonical local-ring maximal ideals,
with the canonical algebra
`Valuation.HasExtension.instAlgebra_valuationSubring` between the valuation
subrings. Mathematically: for an extension of complete discretely valued fields
whose valuation extends the base valuation, and whose valuation ring is
torsion-free over the base valuation ring, the ramification index of the target
maximal ideal over the base maximal ideal is nonzero.

## Implemented proof

The proof is the single term

```lean
Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
  target.maximalIdeal (IsDiscreteValuationRing.not_a_field base.valuationSubring)
```

Mathlib's `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver` states
that if `R` is a domain, `S` is a Dedekind domain torsion-free over `R`,
`P` is a prime of `S` lying over a nonzero ideal `p` of `R`, then
`ramificationIdx' p P ≠ 0`. Its hypotheses are discharged as follows; the
instance names were confirmed by `#synth` in a private development check.

- The torsion-free hypothesis is the retained binder
  `[Module.IsTorsionFree base.valuationSubring target.valuationSubring]`.
- `IsDomain base.valuationSubring` is
  `ValuationSubring.instIsDomainSubtypeMem`.
- `IsDedekindDomain target.valuationSubring` is
  `IsPrincipalIdealRing.isDedekindDomain`, using the discrete valuation ring
  instance `Valuation.valuationSubring_isDiscreteValuationRing` supplied by
  the rank-one discrete valuation of the chosen package.
- `target.maximalIdeal.IsPrime` is `Ideal.IsMaximal.isPrime'`.
- `target.maximalIdeal.LiesOver base.maximalIdeal` is Mathlib's instance
  `Valuation.HasExtension.instLiesOverSubtypeMemValuationSubringValuationSubringMaximalIdeal`
  (in `Mathlib/RingTheory/Valuation/Extension.lean`), derived from the
  valuation extension: the comap of the target maximal ideal is the base
  maximal ideal.
- The nonvanishing `base.maximalIdeal ≠ ⊥` is
  `IsDiscreteValuationRing.not_a_field base.valuationSubring`, since a discrete
  valuation ring is not a field. The `CompleteDVF.maximalIdeal` abbreviation
  unfolds to `IsLocalRing.maximalIdeal base.valuationSubring`, so the types
  agree definitionally.

The development check reports zero errors and zero warnings, and the theorem
depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source correspondence

The source result is `ramificationIndex_ne_zero` in
`LocalFieldTheory.DiscreteValuationField.ValuedExtension`, lines 54–59 of
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationInvariants.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationInvariants.lean#L54-L59)
at NYLL commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`e8f6193618b69865b663a601b6063cbab7231d8ce39259501305d26ffc262e4d`).
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The target's paired Markdown gives the complete statement correspondence,
including the inlining of the source wrapper M108.003,
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
base.toDVF target.toDVF`, by its exact Mathlib body
`Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal`. The algebra map
used by that body (the M108.005 map) is
`algebraMap base.valuationSubring target.valuationSubring` from the canonical
valuation-subring algebra above.

The source proof delegates to
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_ne_zero`,
lines 760–767 of
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteExtension/Degree.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteExtension/Degree.lean#L760-L767)
(file SHA-256
`af4de3740b8a9a4e4717464fe46b5d69a27d7c346aaf327678105a54d00de28d`).
That proof introduces the `LiesOver` fact from its own lemma
`maximalIdeal_liesOver`, applies the same Mathlib lemma with the nonvanishing
proof `base.maximalIdeal_ne_bot`, and unfolds the wrapper by `simpa`. The
adapted proof follows the same route, with these changes:

- the `LiesOver` fact comes from Mathlib's existing instance rather than the
  source lemma;
- the nonvanishing comes from `IsDiscreteValuationRing.not_a_field` rather
  than the source lemma `maximalIdeal_ne_bot`;
- no unfolding step is needed, because the published statement already
  contains the wrapper's Mathlib body.

No source helper lemma is ported. Every mathematical dependency is in the
Library or the pinned Mathlib environment.

## Attribution and modifications

The Lean file retains the original Apache-2.0 copyright and author header:
copyright 2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`),
all rights reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The carried [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged.

The modifications are the `Langlands.NYLL` namespace prefix, the explicit
published `Statement` result type, the single focused import of the statement
module, the inlined wrapper bodies supplied by that statement, and the proof
changes listed above. Worker 308 designed this proof pair (shared draft
revision 1 of Task 6245) and recorded the modification note in the Lean
header. Worker 425 checked it against the original sources, the published
statement and Mathlib, expanded this documentation, and prepared the
submission on 14 November 2026.
