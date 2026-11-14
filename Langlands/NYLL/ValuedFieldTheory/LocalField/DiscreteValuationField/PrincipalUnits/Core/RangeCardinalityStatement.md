# NYLL M231.064: the cardinality of the principal-unit range `U^1/U^n`

Let `F` be a complete discrete valuation field with valuation ring `O`,
maximal ideal `m` and finite residue field `k`. For `n ≥ 0` let
`U^n ≤ Oˣ` be the `n`-th principal-unit subgroup, the units `u` with
`u - 1 ∈ m^n`. If `F` has a uniformizer and `1 ≤ n`, the quotient `U^1/U^n`
has exactly `|k| ^ (n - 1)` elements. This module states that proposition;
it does not prove it.

## Exact target

The declaration is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizerStatement`,
a `def` whose value is a `Prop`. Its universe parameters are `u` (the
field) and `v` (the value group of the chosen valuation); they are
independent, as in the source. Its telescope, in order, is:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K : Type u` | implicit | The field |
| `[Field K]` | instance-implicit | Its field structure |
| `F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K` | explicit | The chosen complete discrete valuation on `K` |
| `[Finite F.residueField]` | instance-implicit | The residue field `k` is finite |
| `pi : F.valuationSubring` | implicit | An element of the valuation ring `O` |
| `hpi : F.valuation.IsUniformizer (pi : K)` | explicit | `pi`, viewed in `K`, is a uniformizer |
| `n : ℕ` | implicit | The upper level |
| `hn : 1 ≤ n` | explicit | The level bound |

The proposition is exactly

```lean
Nat.card (higherPrincipalUnitGroup F 1 ⧸
    (higherPrincipalUnitGroup F n).subgroupOf (higherPrincipalUnitGroup F 1)) =
  Nat.card F.residueField ^ (n - 1)
```

Here `higherPrincipalUnitGroup F 1` is `U^1`, and
`(higherPrincipalUnitGroup F n).subgroupOf (higherPrincipalUnitGroup F 1)`
is `U^n ∩ U^1` regarded as a subgroup of `U^1`; because `1 ≤ n` it is
`U^n` itself. The quotient is Mathlib's coset quotient `G ⧸ H` of the
group `U^1`; its formation needs no normality hypothesis, and `U^n` is
in fact normal because `Oˣ` is commutative. Both sides are natural
numbers: `Nat.card` is Mathlib's cardinality with value `0` on infinite
types, and `n - 1` is natural subtraction, which is the ordinary
difference because `1 ≤ n`. For `n = 1` the formula says that the
trivial quotient `U^1/U^1` has one element.

`hpi` and `hn` do not occur in the defining body, as in the source,
where they are used only by the proof. They are retained with their
source names, explicitness and types. Lean's unused-variables linter
would warn about them, so it is turned off for this one declaration
with `set_option linter.unusedVariables false in`; this affects only
linting, not the meaning of the definition. No other hypothesis is
added and none is removed.

## Interfaces reused

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions`,
which supplies the published M225.001 subgroup
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n : Subgroup F.valuationSubringˣ`
with carrier `{u | (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n}`.
Through it, the published complete-DVF interface supplies the structure
`CompleteDVF.{u,v} K`, whose field `valuation` is a Mathlib
`Valuation K F.ValueGroup` with the published `IsCompleteDiscrete`
instance, and the projections `F.valuationSubring`, `F.maximalIdeal`
and `F.residueField` (the valuation subring, its maximal ideal and its
residue field). The predicate `F.valuation.IsUniformizer` is Mathlib's
`Valuation.IsUniformizer`, meaning that the valuation of `pi` is the
generator below `1` of the value group; its rank-one discrete instance
is the one derived from the published `IsCompleteDiscrete` instance.
No new structure, subgroup, instance or helper declaration is
introduced.

## Source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Core.lean`,
M231.064: theorem
`LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizer`,
docstring at lines 1163–1164, statement at lines 1165–1172, and proof
at lines 1172–1210. The shared parameters are `{K : Type u} [Field K]`
at line 34 and the explicit `F` at line 40; `universe u v` is at line
29. The source file SHA-256 is
`415353484b021d45b0a0d02fe3d57049ec1c92dc8ca8da27477e403b0d1f0604`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`.

Worker 438 extracted the proposition into this focused module. The
modifications are:

- The source namespace
  `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup`
  gains the prefix `Langlands.NYLL`, and the declaration name gains the
  suffix `Statement`.
- The source theorem becomes a `Prop`-valued definition whose body is
  the source proposition verbatim; the source section variable `F` is
  written as the first explicit binder, keeping its type, explicitness
  and position.
- The source imports (Mathlib's ideal-quotient index and the source
  Filtration, AutomorphismTransport, ResidueRoots, ResidueQuotient,
  TeichmullerLift and TeichmullerDecomposition modules) are replaced
  by the single published subgroup module above, which is all the
  proposition needs.
- The source `open ValuationTheory`, `open scoped BigOperators`,
  `open ValuationTheory.DiscreteValuationField.DVF` and
  `noncomputable section` are omitted as unnecessary for the
  proposition; `ValuationTheory.DiscreteValuationField.CompleteDVF`
  resolves to the published Langlands.NYLL structure inside the
  `Langlands.NYLL.LocalFieldTheory` namespace.
- The unused-variables linter is disabled for this declaration, as
  explained above. The module comment and the docstring are new.

## Proof route of the source (not supplied here)

The source proof views `higherPrincipalUnitGroup` as a principal-unit
filtration (M231.020), uses finiteness of its subquotients (M231.018),
writes `|U^1/U^(1+(n-1))|` as the product of the graded pieces
`|U^(1+i)/U^(2+i)|` for `i < n - 1` (M120.074), identifies each graded
piece with `U^(1+i)/U^(2+i)` (M231.033) and uses
`|U^m/U^(m+1)| = |k|` for `m ≥ 1` with the uniformizer `pi` (M231.063).
An exact proof belongs to a separate proof task.

The original copyright and author header is retained; the existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` supply the Apache-2.0
license and attribution.
