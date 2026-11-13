# The pointwise VI.9.6 equivalence from uniform compression stabilization

Author: Worker 151. Module
`Langlands.Representation.Exponents.LeviSecondAdjointnessContragredientEquivalenceReduction`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

This is an internal conditional reduction. It does not prove the unconditional
`LeviSecondAdjointnessContragredientEquivalenceStatement` required by Task 5457.
The additional premise remains an independent proof obligation.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.9.6, printed pp.201–202 / PDF pp.207–208; the stabilization
Proposition is VI.9.1, printed p.197 / PDF p.203, proved in VI.9.2–VI.9.3,
printed pp.198–200 / PDF pp.204–206. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The new proposition records an implication between existing Library
propositions. Its provenance is the composition of published reductions and
proofs below. It does not replace the source's direct proof that its two
Theorems are equivalent.

## Statement

`LeviSecondAdjointnessContragredientEquivalenceReductionStatement.{u,v}`
is the implication

```
RationalPointFamily.UniformCompressionStabilizationStatement.{u, max u v} →
  LeviSecondAdjointnessContragredientEquivalenceStatement.{u,v}.
```

The endpoint is the unchanged Library proposition. In particular it asserts
the equivalence separately for each pair of actual rational parabolics with
the same Levi embedding and the specified intersection of rational-point
images. Both sides use carriers in `max u v`; the field and carrier universe
parameters remain independent. The premise is the existing VI.9.1 dynamic
parabolic statement: its exponent is chosen before all smooth representations,
with both stationary power chains and complementarity, without finiteness
or admissibility conditions on those representations.

## Implemented proof

`leviSecondAdjointnessContragredientEquivalence_of_uniformCompression`
first applies `leviSecondAdjointness_of_structure` with:

- `GroupScheme.parabolicDynamic`;
- `GroupScheme.oppositeDynamicParabolicUniqueness`;
- the supplied uniform compression stabilization premise;
- `GroupScheme.Dynamic.leviAdjointDeterminantReciprocity`;
- `RationalPointFamily.rationalReductiveUnimodularity`;
- `GroupScheme.standardCocharacter`;
- `arbitraryParabolicQuotientCompact`.

Each input other than stabilization is an unconditional published proof of
the exact structural proposition requested by the reduction. This gives
`LeviSecondAdjointnessStatement.{u,v}`. Applying
`leviJacquetContragredient_of_structure` to the first four inputs, with its
carrier universe instantiated as `max u v`, also gives
`LeviJacquetContragredientStatement.{u,max u v}`.

The proof then introduces all binders of the target, installs its canonical
rational-point topology, and specializes both results to that same fixed
pair of parabolics. Each side of the equivalence follows independently
from the stabilization premise, so the two implications are constant maps
to these two proofs. This step proves the pointwise proposition itself;
it does not substitute an equivalence of globally quantified statements.

`leviSecondAdjointnessContragredientEquivalenceReduction` packages this
theorem as a proof of the new named implication.

## Remaining obligation

Uniform compression stabilization is not proved here. Consequently this
module supplies neither an unconditional proof of the exact endpoint nor
a converse derived solely from an arbitrary natural contragredient
isomorphism. The latter would require a separate argument.
