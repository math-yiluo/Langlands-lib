# Images of the base maximal ideal in a finite integral closure

This module defines exactly two closed proposition targets corresponding to
two theorems of Naganori Yamaguchi's NYLL ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, both in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`:

- M245.008,
  [lines 263–289](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean#L263-L289);
- M245.009,
  [lines 291–305](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean#L291-L305).

The entry module is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.IdealImageStatements`.
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
| `ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_base_maximal_map_le_maximalIdeal_of_finite_separable` | `IntegralClosureBaseMaximalMapLeMaximalIdealOfFiniteSeparableStatement.{u, v, w}` | M245.008; `universe u v w` at line 23, ambient variables at 30–31, docstring 263–264, signature 265–271, proof 272–289 |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_base_maximal_map_ne_bot_of_finite_separable` | `IntegralClosureBaseMaximalMapNeBotOfFiniteSeparableStatement.{u, v, w}` | M245.009; same universe line and ambient variables, comment 291–292, `omit [FiniteDimensional K L] in` at 293, docstring 294, signature 295–300, proof 301–305 |

The spelling map adds the `Langlands.NYLL` namespace prefix, converts each
theorem name to PascalCase
(`integralClosure_base_maximal_map_le_maximalIdeal_of_finite_separable`
becomes `IntegralClosureBaseMaximalMapLeMaximalIdealOfFiniteSeparable`, and
`integralClosure_base_maximal_map_ne_bot_of_finite_separable` becomes
`IntegralClosureBaseMaximalMapNeBotOfFiniteSeparable`) and appends
`Statement`. Only universe levels are declaration parameters: each complete,
unapplied constant has type `Prop`, with universe parameters `u, v, w` in that
order.

## Quantifiers

The body of
`IntegralClosureBaseMaximalMapLeMaximalIdealOfFiniteSeparableStatement`
universally quantifies, in order:

```
(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L]
```

These are the source's ambient variables of lines 30–31 followed by the two
binders of the theorem's own signature (lines 266–267), in the source order.
No `omit` directive precedes M245.008, so it keeps `FiniteDimensional K L`.

The body of `IntegralClosureBaseMaximalMapNeBotOfFiniteSeparableStatement`
universally quantifies, in order:

```
(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L]
```

This is the same telescope with `[FiniteDimensional K L]` removed. The source
line 293, `omit [FiniteDimensional K L] in`, removes that ambient instance from
M245.009, so the original theorem does not assume that `L` is
finite-dimensional over `K`. The target follows the source signature, not the
historical theorem name (`..._of_finite_separable`) or the docstring at line
294 ("In a finite separable extension"), which both still mention finiteness.
It keeps `Algebra.IsSeparable K L`. Because the target is a closed
proposition, there are no module-level `variable` lines that could capture a
finiteness instance, and no finiteness hypothesis of any other form
(`Module.Finite`, `FiniteDimensional`, `Algebra.IsIntegral` or a finite
integer module) occurs in its body.

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
maximal ideal. It is used unchanged and with arbitrary data.

## Unfolding of the source abbreviations

The source signatures write `base.maximalIdeal` and `base.valuationSubring`.
As recorded in the published `FiniteIntegralClosure/LocalnessStatements.md`,
these source abbreviations reduce along `CompleteDVF → HenselianDVF → DVF`
(`Complete.lean` lines 118–121, 133 and 137; `Henselian.lean` lines 202 and
206; `Basic.lean` lines 54 and 73) to the subtype
`↥base.valuation.valuationSubring` of Mathlib's `Valuation.valuationSubring`
and to `IsLocalRing.maximalIdeal ↥base.valuation.valuationSubring`. The
targets write these expanded terms directly, as do the published M245.005,
M245.006 and M245.007 declarations.

Write `A := base.valuation.valuationSubring`, `m := IsLocalRing.maximalIdeal A`
and `B := integralClosure A L`. Both bodies have the left side
`m.map (algebraMap A B)`, spelled out in full rather than with `let` binders.
The first concludes

```
m.map (algebraMap A B) ≤ CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base
```

and the second concludes `m.map (algebraMap A B) ≠ ⊥`.

The published module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`
contains adapted aliases `CompleteDVF.valuationSubring` and
`CompleteDVF.maximalIdeal`. A private development check, which imports that
module, confirmed that the source's left side
`base.maximalIdeal.map (algebraMap base.valuationSubring (integralClosure base.valuationSubring L))`
equals the expanded left side by `with_reducible rfl`, and that each target
is equivalent to the source signature written with these aliases and with
implicit `K` and `L`. This module does not import the alias module, so the
targets do not depend on it, and it adds no alias of its own.

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
  `K` followed by the given `algebraMap K L`. No other ring, ideal or scalar
  map is substituted.
- `Ideal.map` (`Mathlib/RingTheory/Ideal/Maps.lean`, line 43) sends `m` to the
  ideal of `B` spanned by its image, `span (algebraMap A B '' m)`, which may be
  larger than the image itself. `≤` is inclusion of ideals of `B`, and `⊥` is
  the zero ideal of `B`.
- The right side of the first target is exactly the published M245.007
  definition
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.CanonicalIntegralClosure.maximalIdeal.{u, v, w}`,
  module `FiniteIntegralClosure.MaximalIdeal`, applied with `K`, `L`, the
  binders above and `base`. It installs the published M245.006 localness
  theorem as a local witness and returns `IsLocalRing.maximalIdeal B`, the
  ideal of non-units of the actual integral closure. A private check
  confirmed after `delta` that it equals
  `@IsLocalRing.maximalIdeal B _ (integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base)`
  by `with_reducible rfl`. The target does not repeat this construction and
  does not take an `IsLocalRing B` premise: without the local witness, instance
  search finds no `IsLocalRing B`.

When the bodies are elaborated, Lean abstracts three instance proofs into
auxiliary theorems attached to the first target:
`IntegralClosureBaseMaximalMapLeMaximalIdealOfFiniteSeparableStatement._proof_1`
and `._proof_2`, both of type `SubsemiringClass (ValuationSubring K) K`, and
`._proof_3`, whose value is `ValuationSubring.isLocalRing` for `A`. The second
target's body reuses these same auxiliary proofs. They concern only the
valuation subring of `K`, mention neither `L` nor finite dimensionality, and
prove nothing about either target.

## Mathematical meaning

`IntegralClosureBaseMaximalMapLeMaximalIdealOfFiniteSeparableStatement` says:
for every field `K` with a chosen complete discrete valuation `base`, with
valuation ring `A` and maximal ideal `m`, and every finite separable field
extension `L` of `K`, the ideal generated by `m` in the integral closure `B`
of `A` in `L` is contained in the canonical maximal ideal of `B` (the ideal of
non-units of `B`, which is local by M245.006).

`IntegralClosureBaseMaximalMapNeBotOfFiniteSeparableStatement` says: for every
field `K` with a chosen complete discrete valuation `base` and every separable
algebraic field extension `L` of `K`, with no finiteness assumption, the ideal
generated by `m` in `B` is nonzero. It neither uses nor states the first
target, and it does not mention `CanonicalIntegralClosure.maximalIdeal`.

Neither body adds an `IsLocalRing B`, `IsLocalHom`, injectivity,
`FaithfulSMul`, nonzero-ideal, discrete valuation ring, `Module.Finite`,
chosen extension valuation, extension record or any other conclusion-like
premise. Neither assumes that `L` is a proper or nontrivial extension of `K`.
The completeness and discreteness of the base enter only through the
`CompleteDVF` structure.

## Independent universes

The source declares `universe u v w` (line 23), binds `K : Type u` and
`L : Type w` (line 30) and uses `CompleteDVF.{u, v} K`, whose value group lies
in `Type v`. Both targets keep these three independent levels: the base field,
the value group and the extension field may lie in unrelated universes.
Neither target identifies universes or restricts to `Type 0`.

## Checks

The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Inspection of each declaration
reports `statement_returns_prop: true`, universe parameters `u, v, w` and only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`. Neither
definition is an instance.

Private checks, which are not part of the module, confirm the following.

- Each body has exactly the binders displayed above, with the stated binder
  kinds, in that order.
- After `delta`, each target equals its displayed body, written with the
  expanded objects and with `@CanonicalIntegralClosure.maximalIdeal.{u, v, w}`
  applied to `K`, `L`, the instances and `base`, by `with_reducible rfl`.
- Each target is equivalent to the source signature written with the
  `Complete.Projections` aliases and implicit `K` and `L`.
- The value of the second target uses neither `FiniteDimensional` nor
  `Module.Finite`, and it applies to `K`, `L` and `base` with no
  finite-dimensionality instance in context.
- The scalar map equalities and the M245.007 unfolding stated above hold, and
  there is no global `IsLocalRing B` instance.

## Imports and reuse

The direct imports are:

- the published
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdeal`,
  providing `CanonicalIntegralClosure.maximalIdeal` and, through its imports,
  `CompleteDVF`, `integralClosure`, `FiniteDimensional`,
  `Algebra.IsSeparable` and `IsLocalRing.maximalIdeal`;
- `Mathlib.RingTheory.Ideal.Maps`, providing `Ideal.map`.

The source file imports
`Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core`
and `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`; these
are needed only by the omitted proofs and the other declarations of the file.
`FiniteExtension.Core` is not ported, and no unpublished NYLL module is
imported. M245.007 and the localness theorem are reused by name, not
duplicated.

TaskHub tasks, the current Library and the pinned Mathlib were searched by
the original and adapted names and for results on the image of the base
maximal ideal in an integral closure. These bounded searches found no
existing declaration stating either target. Mathlib's
`IsLocalRing.local_hom_TFAE`
(`Mathlib/RingTheory/LocalRing/RingHom/Basic.lean`, line 80),
`Ideal.map_eq_bot_iff_of_injective` (`Ideal/Maps.lean`, line 1062) and
`Ideal.map_ne_bot_of_ne_bot` (`Ideal/Maps.lean`, line 1132) are tools for later proofs, not proofs of these
targets.

For provenance only: the original M245.008 proof installs the M245.006
localness witness on `B`, shows that `algebraMap A B` is a local homomorphism
because `B` is integral over `A` and the map is injective (the source's
M245.001 wrapper `CanonicalIntegralClosure.algebraMap_injective`), and
concludes with `IsLocalRing.local_hom_TFAE`. The original M245.009 proof
combines the same injectivity with `Ideal.map_eq_bot_iff_of_injective` and
the source lemma `base.maximalIdeal_ne_bot`. No original proof is included in,
or claimed as an implemented proof by, this statement module.

## Scope

This unit contains only these two statements. It does not state or prove the
other declarations of FiniteIntegralClosure.lean, including the M245.001 and
M245.002 wrappers, the M245.003 and M245.004 completeness and Henselian
statements, the M245.005 and M245.006 fiber and localness statements, the
M245.007 maximal ideal (which it imports), M245.010 (`B` is not a field),
M245.011 (`B` is a discrete valuation ring) or M245.012 onward. It makes no
claim about chosen extension valuations, complete local field packaging,
integer-ring comparison, residue actions, inertia or reciprocity, and adds no
global instance, theorem or public data alias.

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
explicit independent universe parameters, kept the source's omission of
`FiniteDimensional K L` for M245.009, added the namespace prefix and target
names, unfolded the source abbreviations `base.valuationSubring` and
`base.maximalIdeal`, reduced the imports to the published M245.007 module and
one Mathlib module, and wrote this Markdown. The Lean header records these
modifications. Worker 106 supplied routing only, no implementation draft. No
other worker's adapted Lean content was used.
