# The base maximal ideal as a power of the canonical maximal ideal

This module defines exactly two closed proposition targets corresponding to
two theorems of Naganori Yamaguchi's NYLL ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, both in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`:

- M245.012,
  [lines 355–388](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean#L355-L388);
- M245.013,
  [lines 389–426](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean#L389-L426).

The entry module is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.IdealPowerStatements`.
These definitions name propositions; they contain no proofs of the
propositions. Publishing them proves neither assertion. A subsequent proof
must establish each published target separately.

## Exact source correspondence

Both adapted names belong to
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension`. The
source namespace is `ValuationTheory.DiscreteValuationField.ValuedExtension`
(source lines 17, 25 and 26).

| Source theorem | Closed proposition target | Source unit and lines |
| --- | --- | --- |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow` | `ExistsIntegralClosureBaseMaximalMapEqMaximalIdealPowStatement.{u, v, w}` | M245.012; `universe u v w` at line 23, ambient variables at 30–31, docstring 355–356, signature 357–364, proof 365–387 |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow_pos` | `ExistsIntegralClosureBaseMaximalMapEqMaximalIdealPowPosStatement.{u, v, w}` | M245.013; same universe line and ambient variables, docstring 389–390, signature 391–399, proof 400–426 |

The spelling map adds the `Langlands.NYLL` namespace prefix, converts each
theorem name to PascalCase
(`exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow` becomes
`ExistsIntegralClosureBaseMaximalMapEqMaximalIdealPow`, and
`exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow_pos` becomes
`ExistsIntegralClosureBaseMaximalMapEqMaximalIdealPowPos`) and appends
`Statement`. Only universe levels are declaration parameters: each complete,
unapplied constant has type `Prop`, with universe parameters `u, v, w` in that
order.

## Quantifiers

The bodies of both targets universally quantify, in order:

```
(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L]
```

These are the source's ambient variables of lines 30–31 followed by the two
binders of each theorem's own signature (lines 358–359 and 392–393), in the
source order. The only `omit [FiniteDimensional K L] in` directives in the
source file are at lines 35, 51, 293 and 309, and the file has no other
`omit`, `include` or `variable` line after line 31. Neither M245.012 nor
M245.013 is preceded by an `omit` directive, so both keep
`FiniteDimensional K L`, and both keep `Algebra.IsSeparable K L`.

The source binds `K` and `L` implicitly and `base` explicitly; inside a
universally quantified proposition the explicit binders used here state the
same mathematics, and the instance-implicit binders are the source's.

`CompleteDVF.{u, v} K` is the published structure from
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`
(source unit M107.006): a value group `ValueGroup : Type v` with a
`LinearOrderedCommGroupWithZero` structure, a valuation
`valuation : Valuation K ValueGroup`, and an instance
`Valuation.IsCompleteDiscrete valuation`, which says that the valuation is
rank-one discrete and that its valuation subring is adically complete for its
maximal ideal. It is used unchanged and with arbitrary data, and the
`Algebra K L` structure is the arbitrary supplied one.

## Unfolding of the source abbreviations

The source signatures write `base.maximalIdeal` and `base.valuationSubring`.
As recorded in the published `FiniteIntegralClosure/LocalnessStatements.md`
and `FiniteIntegralClosure/IdealImageStatements.md`, these source
abbreviations reduce along `CompleteDVF → HenselianDVF → DVF`
(`Complete.lean` lines 118–121, 133 and 137; `Henselian.lean` lines 202 and
206; `Basic.lean` lines 54 and 73) to the subtype
`↥base.valuation.valuationSubring` of Mathlib's `Valuation.valuationSubring`
and to `IsLocalRing.maximalIdeal ↥base.valuation.valuationSubring`. The
targets write these expanded terms directly, as do the published M245.005 to
M245.009 declarations.

Write `A := base.valuation.valuationSubring`, `m := IsLocalRing.maximalIdeal A`,
`B := integralClosure A L` and
`M := CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base`. These are
abbreviations of this text only; the module declares no such names. The bodies
spell the terms out in full, without `let` binders. The first concludes

```
∃ n : ℕ, m.map (algebraMap A B) = M ^ n
```

and the second concludes

```
∃ n : ℕ, 0 < n ∧ m.map (algebraMap A B) = M ^ n
```

The published module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`
contains adapted aliases `CompleteDVF.valuationSubring` and
`CompleteDVF.maximalIdeal`. A private development check, which imports that
module, confirmed that each target is equivalent to the source signature
written with these aliases and with implicit `K` and `L`. This module does not
import the alias module, so the targets do not depend on it, and it adds no
alias of its own.

## Objects in the statements

- `A` carries Mathlib's ring and local ring structures on a valuation
  subring: `ValuationSubring.instCommRingSubtypeMem` and
  `ValuationSubring.isLocalRing`
  (`Mathlib/RingTheory/Valuation/ValuationSubring.lean`, line 148). These
  are the structures the source installs (`Basic.lean` lines 58–66). `m` is
  Mathlib's `IsLocalRing.maximalIdeal`
  (`Mathlib/RingTheory/LocalRing/MaximalIdeal/Defs.lean`, line 30), the ideal
  of non-units of `A`.
- `Algebra A L` is Mathlib's `Algebra.ofSubsemiring` instance for the subring
  `A` of `K` (`Mathlib/Algebra/Algebra/Basic.lean`, line 101), with algebra
  map `(algebraMap K L).comp (algebraMap A K)`.
- `B` is Mathlib's actual subalgebra `integralClosure A L`
  (`Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`, line 216): the
  elements of `L` that are integral over `A`, as a ring through the
  subalgebra structure. Nothing about `B` is assumed beyond this definition.
- `algebraMap A B` is the structure map of `Subalgebra.algebra`
  (`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`, line 336): the
  corestriction of `A → L` to `B`. A development check confirmed by `rfl`
  that its composite with the inclusion `B → L` equals
  `(algebraMap K L).comp (algebraMap A K)`, that is, the inclusion of `A` into
  `K` followed by the supplied `algebraMap K L`. No other ring, ideal or
  scalar map is substituted.
- `Ideal.map` (`Mathlib/RingTheory/Ideal/Maps.lean`, line 43) sends `m` to the
  ideal of `B` spanned by its image, `span (algebraMap A B '' m)`, which may be
  larger than the image itself.
- `M` is exactly the published M245.007 definition
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.CanonicalIntegralClosure.maximalIdeal.{u, v, w}`,
  module `FiniteIntegralClosure.MaximalIdeal`, applied with `K`, `L`, the
  binders above and `base`. It installs the published M245.006 localness
  theorem as a local witness and returns `IsLocalRing.maximalIdeal B`, the
  ideal of non-units of the actual integral closure. A private check
  confirmed after `delta` that it equals
  `@IsLocalRing.maximalIdeal B _ (integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base)`
  by `with_reducible rfl`. The targets do not repeat this construction and
  do not take an `IsLocalRing B` premise: without the local witness, instance
  search finds no `IsLocalRing B`.
- `M ^ n` is Mathlib's power of submodules, the instance
  `Submodule.instPowNat` (`Mathlib/Algebra/Algebra/Operations.lean`,
  line 311), for `B` as a module over itself. It is defined by `npowRec`, so
  `M ^ 0 = 1` and `M ^ (n + 1) = M ^ n * M` by definition
  (`Submodule.pow_zero` and `Submodule.pow_succ`, lines 321 and 323), where
  `*` is the product of ideals. For ideals `1 = ⊤`
  (`Ideal.one_eq_top`, `Mathlib/RingTheory/Ideal/Operations.lean`, line 271),
  so `M ^ 0` is the unit ideal of `B`; a private check confirmed both facts
  for `M`. This is the power used by the original statements and by Mathlib
  lemmas such as `Ideal.span_singleton_pow`.
- `n` ranges over the natural numbers `ℕ`, and `0 < n` is the usual order on
  `ℕ`. The equality `=` is equality of ideals of `B`.

When the bodies are elaborated, Lean abstracts four instance proofs into
auxiliary theorems attached to the first target:
`ExistsIntegralClosureBaseMaximalMapEqMaximalIdealPowStatement._proof_1`
and `._proof_2`, both of type `SubsemiringClass (ValuationSubring K) K`;
`._proof_3`, whose value is `ValuationSubring.isLocalRing` for `A`; and
`._proof_4`, of type `IsScalarTower B B B` with value
`IsScalarTower.right` (`Mathlib/Algebra/Algebra/Defs.lean`, line 308), which
the submodule power requires. The second target's body reuses these same
auxiliary proofs. A private check listed the module's constants: exactly the
two targets and these four auxiliary theorems. The auxiliary theorems prove
only instance facts about `A` and `B` and nothing about either target.

## Mathematical meaning

`ExistsIntegralClosureBaseMaximalMapEqMaximalIdealPowStatement` says: for
every field `K` with a chosen complete discrete valuation `base`, with
valuation ring `A` and maximal ideal `m`, and every finite separable field
extension `L` of `K`, the ideal generated by `m` in the integral closure `B`
of `A` in `L` equals some power `M ^ n` of the canonical maximal ideal `M` of
`B` (the ideal of non-units of `B`, which is local by M245.006). The exponent
`n = 0` is not excluded by this statement; it would mean that the ideal
generated by `m` is all of `B`.

`ExistsIntegralClosureBaseMaximalMapEqMaximalIdealPowPosStatement` is the
positive-exponent variant: under the same hypotheses, the ideal generated by
`m` in `B` equals `M ^ n` for some `n ≥ 1`. It strengthens the first target;
a private check confirmed that it implies the first by forgetting `0 < n`.
In standard terminology the exponent is the ramification index of `L` over
`K`, but neither target names, characterizes or computes that number, and
neither states that `n` is unique.

Neither body adds an `IsLocalRing B`, `IsDiscreteValuationRing B`,
`IsDedekindDomain B`, injectivity, `FaithfulSMul`, nonzero or proper mapped
ideal, containment `m.map (algebraMap A B) ≤ M`, principal-ideal
classification, chosen uniformizer, ideal-power equality, positive-exponent or
any other conclusion-like premise. Neither takes an arbitrary upstairs ideal,
a chosen extension valuation or an isomorphic auxiliary ring in place of the
actual integral closure and its canonical ideal. Neither assumes that `L` is a
proper or nontrivial extension of `K`. The completeness and discreteness of
the base enter only through the `CompleteDVF` structure.

## Independent universes

The source declares `universe u v w` (line 23), binds `K : Type u` and
`L : Type w` (line 30) and uses `CompleteDVF.{u, v} K`, whose value group lies
in `Type v`. Both targets keep these three independent levels: the base field,
the value group and the extension field may lie in unrelated universes.
Neither target identifies universes or restricts to `Type 0`.

## Checks

The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Inspection of each declaration
reports kind `definition`, `statement_returns_prop: true`, universe
parameters `u, v, w` and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. Neither definition is an instance.

Private checks, which are not part of the module, confirm the following.

- Each body has exactly the binders displayed above, with the stated binder
  kinds, in that order.
- After `delta`, each target equals its displayed body, written with the
  expanded objects and with `@CanonicalIntegralClosure.maximalIdeal.{u, v, w}`
  applied to `K`, `L`, the instances and `base`, by `with_reducible rfl`.
- Each target is equivalent to the source signature written with the
  `Complete.Projections` aliases and implicit `K` and `L`.
- The positive-exponent target implies the first target.
- The scalar map equality, the M245.007 unfolding and the power facts stated
  above hold, and there is no global `IsLocalRing B` instance.
- Neither value mentions the constants `IsLocalRing` or
  `IsDiscreteValuationRing` directly; local ring structures enter only
  through `._proof_3` for `A` and through M245.007 for `M`.

## Imports and reuse

The direct imports are:

- the published
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdeal`,
  providing `CanonicalIntegralClosure.maximalIdeal` and, through its imports,
  `CompleteDVF`, `integralClosure`, `FiniteDimensional`,
  `Algebra.IsSeparable` and `IsLocalRing.maximalIdeal`;
- `Mathlib.RingTheory.Ideal.Maps`, providing `Ideal.map` and, through its
  imports, the product and power of ideals.

The source file imports
`Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core`
and `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`; these
are needed only by the omitted proofs and the other declarations of the file.
`FiniteExtension.Core` is not ported, and no unpublished NYLL module is
imported. M245.007 and the localness theorem are reused by name, not
duplicated.

TaskHub tasks, the current Library, staging and the pinned Mathlib were
searched by the original and adapted names and for results on the image of
the base maximal ideal in an integral closure as a power of its maximal
ideal. These bounded searches found no existing declaration stating either
target. `Langlands.PadicField.TopologicalData.map_maximalIdeal_of_ramificationIndex_eq_mul`
and its variants in `Langlands.LocalField.RelativeIdealPowers` concern
supplied host integer rings and a ramification-index equation, not the
actual integral closure with its canonical ideal, and are not these
existence statements.

Already published results that are tools for later proofs, not premises of
these targets, include `integralClosure_isDiscreteValuationRing_of_finite_separable`
(M245.011, module `FiniteIntegralClosure.DVRProof`),
`integralClosure_base_maximal_map_le_maximalIdeal_of_finite_separable` and
`integralClosure_base_maximal_map_ne_bot_of_finite_separable` (M245.008 and
M245.009, module `FiniteIntegralClosure.IdealImageProofs`), and Mathlib's
`IsDiscreteValuationRing.exists_irreducible` and
`IsDiscreteValuationRing.ideal_eq_span_pow_irreducible`
(`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`, lines 105 and 364),
`Irreducible.maximalIdeal_eq` (same file, line 98) and
`Ideal.span_singleton_pow` (`Mathlib/RingTheory/Ideal/Operations.lean`,
line 420).

For provenance only: the original M245.012 proof installs the M245.006
localness witness on `B`, makes `B` a discrete valuation ring by M245.011,
uses M245.009 to see that the mapped ideal is nonzero, and writes it as a
power of the ideal spanned by a uniformizer with
`IsDiscreteValuationRing.ideal_eq_span_pow_irreducible`. The original
M245.013 proof applies M245.012 and excludes `n = 0`: the mapped ideal would
then be the unit ideal, contradicting its containment in the proper ideal `M`
(M245.008). No original proof is included in, or claimed as an implemented
proof by, this statement module.

## Scope

This unit contains only these two statements. It does not state or prove the
other declarations of FiniteIntegralClosure.lean, including the M245.001 to
M245.006 wrappers and theorems, the M245.007 maximal ideal (which it imports),
M245.008 to M245.011, the M245.014 completeness result for `M` or the
valuation-existence and uniqueness results from M245.015 onward. It makes no
claim about chosen extension valuations, complete local field packaging,
host integer-ring comparison, residue actions, inertia or reciprocity, and
adds no global instance, theorem or public data alias.

## Source record and attribution

The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its local source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The original file's verified SHA256 is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`. The
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`; its
ValuedFieldTheory third-party source table does not list
FiniteIntegralClosure.lean, and NOTICE has no source-specific entry for it,
so no further third-party attribution applies. The published source partition
`notes/reuse/nyll-public-port/m241-m258.md` records no patch for M245, and no
applicable erratum was found in the project or the published NYLL notes at
extraction time.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, authors Naganori Yamaguchi (assisted by OpenAI Codex),
released under Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany the extraction.

Worker 1045 extracted the two original theorem signatures on
30 October 2026, closed their quantifiers inside Prop-valued definitions with
explicit independent universe parameters, added the namespace prefix and
target names, unfolded the source abbreviations `base.valuationSubring` and
`base.maximalIdeal`, reduced the imports to the published M245.007 module and
one Mathlib module, and wrote this Markdown. The Lean header records these
modifications. Worker 106 supplied routing only, no implementation draft. No
other worker's adapted Lean content was used.
