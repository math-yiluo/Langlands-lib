# Reduction of common-closure spectral analyticity to rank one

Worker 1237 derives this component from the published common-closure
induction, spectral twist, system and degree-zero generation definitions. It
introduces no reciprocity family, local-constant system or generation
assumption of its own. Generation and rank-one analyticity enter only as
explicit hypotheses of `analyticAt_of_generation`. The module does not prove
`CommonClosureSpectralAnalyticStatement` by itself. It reduces analyticity
for arbitrary exact virtual classes to analyticity for rank-one classes, through
the induction relation.

## Induction and twisting

For nested intermediate fields `E ≤ L` with `h : E.field ≤ L.field`,
`character_nestedWeilEquiv` states that the spectral character of `L`, composed
with the nested-subgroup equivalence `nestedWeilEquiv F E L h`, equals the
spectral character of `E` restricted to the same nested subgroup. Both send an
element `w` to `exp(-s log q)^(deg w)`. Here `q` is the base residue
cardinality and `deg w` is the base-field degree of `w` in the ambient Weil
group. The proof is definitional (`ext w; rfl`).

`virtualTwist_induce` proves, for every complex `s` and every exact virtual
class `x` over `L`,

```
virtualTwist F E s (induce F E L h x) = induce F E L h (virtualTwist F L s x).
```

The proof unfolds `induce` into actual continuous restriction along the nested
equivalence followed by continuous induction from the open nested subgroup. It
then applies the published projection laws
`ExactGrothendieckGroup.continuousRestrict_continuousTwist` and
`ExactGrothendieckGroup.continuousInduce_continuousTwist`, with
`character_nestedWeilEquiv` between them.

## The analytic subgroup

`haarMeasure_nonempty E` produces a Haar measure on every intermediate field:
the normalized additive Haar measure of a positive compact set. This set
exists because the field is locally compact.

`RankOneAnalytic ε` is the proposition that, for every intermediate field `L`,
additive character `ψ`, Haar measure `μ`, continuous character
`χ : weilSubgroup F L →ₜ* ℂˣ` and complex point `s`, the function
`z ↦ ε L ψ μ (virtualTwist F L z (characterClass χ))` is complex-analytic at
`s`. It is a proposition about the supplied assignment `ε`, not an assumption
of the module.

For a system `hε : IsSystem F e ε`, an intermediate field `E`, an additive
character `ψ` and a Haar measure `μ`, `analyticSubgroup hε E ψ μ` is the set
of exact virtual classes `x` over `E` for which
`z ↦ conditionalDeligneValue F e ε hε E ψ μ x z` is analytic at every complex
point. It is an additive subgroup. The value of `0` is the constant `1` by
`value_zero`. By the additivity relation `hε.2.1` and the linearity of the
spectral twist, a sum has the product of the two values, and a negative has
the inverse value (`value_neg`). Products of analytic functions are analytic,
and so are inverses of nonvanishing analytic functions; every value is a unit.
`mem_analyticSubgroup` unfolds membership.

## Generators and the reduction

`generators_subset_analyticSubgroup` assumes `RankOneAnalytic ε`. It proves that
every element of `characterDifferenceInductionGenerators F E` lies in the
analytic subgroup. Such an element is `induce F E L h (class χ - class χ')`.
Choose a Haar measure `μL` on `L`. At each `z`, `virtualTwist_induce` moves the
twist inside the induction. The twisted difference still has degree zero
because twisting preserves degree (`degree_virtualTwist`). The induction
relation `hε.2.2.2.1` then rewrites the value over `E` as the value over `L` at
the trace character `traceCharacter F E L h ψ` and `μL`. Additivity writes that
value as the value of `class χ` times the inverse of the value of `class χ'`.
Both factors are analytic by `RankOneAnalytic ε`.

`analyticAt_of_generation` assumes `CommonClosureDegreeZeroGeneration F`, a
system `hε`, and `RankOneAnalytic ε`. It concludes, for every intermediate
field `E`, additive character `ψ`, Haar measure `μ`, exact virtual class `x` and
complex point `s`, that `z ↦ conditionalDeligneValue F e ε hε E ψ μ x z` is
analytic at `s`. Generation identifies the integer span of the generators with
`DegreeZero F E`. The span lies in the analytic subgroup by the previous
theorem, so every degree-zero class does. The trivial character class `t` has
degree one and lies in the subgroup by `RankOneAnalytic ε`. Finally `x` is the
sum of the degree-zero class `x - (degree x) • t` and `(degree x) • t`.

Field and representation-carrier universes `uF` and `uV` stay independent
throughout.
