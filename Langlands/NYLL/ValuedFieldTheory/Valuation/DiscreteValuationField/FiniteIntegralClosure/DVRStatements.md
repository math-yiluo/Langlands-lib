# Integral closures over complete DVFs: not a field, and a DVR

This module defines exactly two closed proposition targets corresponding to
two theorems of Naganori Yamaguchi's NYLL ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, both in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`:

- M245.010,
  [lines 307–327](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean#L307-L327);
- M245.011,
  [lines 329–353](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean#L329-L353).

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
| `ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_not_isField_of_finite_separable` | `IntegralClosureNotIsFieldOfFiniteSeparableStatement.{u, v, w}` | M245.010; `universe u v w` at line 23, ambient variables at 30–31, comment 307–308, `omit [FiniteDimensional K L] in` at 309, docstring 310, signature 311–314, proof through 327 |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_isDiscreteValuationRing_of_finite_separable` | `IntegralClosureIsDiscreteValuationRingOfFiniteSeparableStatement.{u, v, w}` | M245.011; same universe line and ambient variables, docstring 329–330, signature 331–334, proof through 353 |

The spelling map adds the `Langlands.NYLL` namespace prefix, converts each
theorem name to PascalCase
(`integralClosure_not_isField_of_finite_separable` becomes
`IntegralClosureNotIsFieldOfFiniteSeparable`, and
`integralClosure_isDiscreteValuationRing_of_finite_separable` becomes
`IntegralClosureIsDiscreteValuationRingOfFiniteSeparable`) and appends
`Statement`. Only universe levels are declaration parameters: each complete,
unapplied constant has type `Prop`, with universe parameters `u, v, w` in that
order.

## Quantifiers

`IntegralClosureNotIsFieldOfFiniteSeparableStatement` universally quantifies,
in order:
`(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L]`.

`IntegralClosureIsDiscreteValuationRingOfFiniteSeparableStatement`
universally quantifies, in order:
`(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] (base : CompleteDVF.{u, v} K)
[Algebra.IsSeparable K L]`.

These are the source's ambient variables of lines 30–31 followed by the two
binders of each theorem's own signature, in the source order. The only
difference between the two telescopes is the source's
`omit [FiniteDimensional K L] in` at line 309, which removes the ambient
finite-dimensionality instance from M245.010 alone; M245.011 is not covered by
an `omit` clause and keeps it. Both keep `[Algebra.IsSeparable K L]`, which is
an explicit binder of both source signatures (lines 313 and 333). The source
binds `K` and `L` implicitly and `base` explicitly; inside a universally
quantified proposition the explicit binders used here state the same
mathematics, and the instance-implicit binders are the source's.

`CompleteDVF.{u, v} K` is the published structure from
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`
(source unit M107.006): a value group `ValueGroup : Type v` with a
`LinearOrderedCommGroupWithZero` structure, a valuation
`valuation : Valuation K ValueGroup`, and an instance
`Valuation.IsCompleteDiscrete valuation`, which says that the valuation is
rank-one discrete and that its valuation subring is adically complete for its
maximal ideal. It is used unchanged; the complete discrete valuation data and
the `K`-algebra structure on `L` are arbitrary.

## Scope of M245.010 compared with its name and docstring

The source name says `finite_separable`, the comment at lines 307–308 says "In
a finite separable extension", and the docstring at line 310 says "The integral
closure in a nontrivial finite separable extension is not a field". The source
signature nevertheless assumes neither finiteness nor nontriviality: line 309
omits `[FiniteDimensional K L]`, and no binder requires `L ≠ K`, a degree
bound or a proper extension. The target follows the signature, not the prose:

- it assumes no `FiniteDimensional K L`, so it covers every separable field
  extension, finite or infinite (by Mathlib's `Algebra.IsSeparable.isIntegral`,
  `Mathlib/FieldTheory/Separable.lean` line 566, every such extension is
  integral, hence algebraic);
- it assumes no nontriviality, so it also covers `L = K` and any isomorphic
  copy of `K`;
- it keeps the name and the `[Algebra.IsSeparable K L]` hypothesis of the
  source, so it is stronger than its name suggests in finiteness but not
  generalized by dropping separability.

The Lean docstring of the target is reworded accordingly; the source wording
"finite" and "nontrivial" adds no hypothesis here. For provenance only: the
steps of the source proof at lines 315–327 cite no separability or
finite-dimensionality fact, but the target keeps separability as the source
signature does, and a later proof may use it or not.

`IntegralClosureIsDiscreteValuationRingOfFiniteSeparableStatement` keeps both
`[FiniteDimensional K L]` and `[Algebra.IsSeparable K L]`, so it is a statement
about finite separable extensions exactly as its name says (the trivial
extension is not excluded there either).

## Unfolding of the source abbreviation

The source signatures write `integralClosure base.valuationSubring L`. In the
source, `base.valuationSubring` is an abbreviation along the path
`CompleteDVF → HenselianDVF → DVF`:
`CompleteDVF.valuationSubring F := F.toHenselianDVF.valuationSubring`
(`Complete.lean` line 133), `HenselianDVF.valuationSubring F :=
F.toDVF.valuationSubring` (`Henselian.lean` line 202) and
`DVF.valuationSubring F := F.valuation.valuationSubring` (`Basic.lean`
line 54), where `toHenselianDVF` builds its DVF with
`valuation := F.valuation` (`Complete.lean` lines 118–121). So
`base.valuationSubring` is the subtype `↥base.valuation.valuationSubring` of
Mathlib's `Valuation.valuationSubring`. The source's ring structure on it is
Mathlib's: its instance `DVF.valuationSubring.commRing` is
`ValuationSubring.instCommRingSubtypeMem` (`Basic.lean` lines 57–60), and Lean
synthesizes exactly this instance in the targets.

The targets write this term directly. Writing
`A := ↥base.valuation.valuationSubring` and `B := integralClosure A L`, the
first body concludes `¬ IsField B` and the second concludes
`IsDiscreteValuationRing B`; the Lean bodies spell out `A` and `B` in full
rather than using `let` binders.

The published module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`
contains the adapted alias `CompleteDVF.valuationSubring`. A private
development check confirmed that `base.valuationSubring =
↥base.valuation.valuationSubring`, `integralClosure base.valuationSubring L =
integralClosure ↥base.valuation.valuationSubring L` and the corresponding
equality of the `IsField` propositions all hold by `with_reducible rfl`, and
that the source-form and target-form `IsDiscreteValuationRing` propositions
are equivalent by `Iff.rfl`. This
module does not import that alias module, so the targets do not depend on it,
and it adds no alias of its own. M245.007's published maximal-ideal data is
not needed by either conclusion and is not imported.

## Scalar structures, integral closure and conclusions

- `Algebra A L` is Mathlib's `Algebra.ofSubsemiring` instance for the
  subring `A` of `K` (`Mathlib/Algebra/Algebra/Basic.lean`, lines 100–102).
  Its algebra map is `(algebraMap K L).comp (algebraMap A K)`: the inclusion
  of `A` into `K` followed by the supplied structure map `K → L`. A
  development check confirmed this equality by `rfl`.
- `integralClosure A L` is Mathlib's `integralClosure`
  (`Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`, line 216): the
  `A`-subalgebra of `L` whose elements are the elements of `L` integral over
  `A`. `B` is its coercion to a type. Its semiring structure, used by
  `IsField`, is `Subalgebra.toSemiring`, and its commutative ring structure,
  used by `IsDiscreteValuationRing`, is `Subalgebra.toCommRing`, both
  restricted from `L`. Its canonical map from `A` is the corestriction of the
  algebra map above; a development check confirmed by `rfl` that composing it
  with the inclusion of `B` in `L` gives `algebraMap A L`. Nothing about `B` is assumed beyond this definition: it
  is the actual integral closure inside the given `L`, not an isomorphic
  auxiliary ring or the valuation ring of a chosen extension valuation.
- `IsField R` (`Mathlib/Algebra/Field/IsField.lean`, lines 33–39) is the
  structure saying that the semiring `R` has two distinct elements, is
  commutative and has inverses of all nonzero elements. The first target
  concludes its negation for `B`.
- `IsDiscreteValuationRing R` (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`,
  lines 56–60) requires `[CommRing R] [IsDomain R]` and says that `R` is a
  principal ideal ring and a local ring whose maximal ideal is not `⊥`. In the
  second target the `IsDomain B` argument is the Mathlib instance
  `instIsDomainSubtypeMemSubalgebraIntegralClosure`
  (`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`,
  lines 659–660), obtained because `L` is a field; it is a proof of a
  proposition, synthesized rather than assumed, so it adds no hypothesis.

## Mathematical meaning

`IntegralClosureNotIsFieldOfFiniteSeparableStatement` says: for every field
`K` with a chosen complete discrete valuation `base`, with valuation ring
`A`, and every separable field extension `L` of `K` (with no finiteness
condition), the integral closure `B` of `A` in `L` is not a field.

`IntegralClosureIsDiscreteValuationRingOfFiniteSeparableStatement` says: for
the same data and with `L` finite-dimensional over `K`, the integral closure
`B` is a discrete valuation ring.

The targets do not take each other, M245.006 localness or any other
conclusion as a premise. Neither body adds `IsLocalRing B`, `IsDomain B` as a
hypothesis, `IsDedekindDomain`, `IsNoetherianRing`, `IsFractionRing A K`,
`FaithfulSMul A B`, injectivity of `A → B`, `Module.Finite A B`, a chosen
extension valuation, `Valuation.HasExtension`, a topology, an extension record
or any other conclusion-like certificate. The completeness of the base enters
only through the `CompleteDVF` structure.

## Independent universes

The source declares `universe u v w` (line 23), binds `K : Type u` and
`L : Type w` (line 30) and uses `CompleteDVF.{u, v} K`, whose value group lies
in `Type v`. Both targets keep these three independent levels: the base field,
the value group and the extension field may lie in unrelated universes.
Neither target identifies universes or restricts to `Type 0`.

## Imports and reuse

The direct imports are:

- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`,
  providing `CompleteDVF` and, through its Mathlib imports,
  `Valuation.valuationSubring`;
- `Mathlib.Algebra.Field.IsField`, providing `IsField`;
- `Mathlib.FieldTheory.Separable`, providing `Algebra.IsSeparable`;
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, providing
  `FiniteDimensional`;
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`, providing
  `IsDiscreteValuationRing`;
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, providing
  `integralClosure`;
- `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`, providing the
  `IsDomain` instance on `integralClosure A L`.

The source file imports
`Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core`
and `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`; these
are needed only by the omitted proofs and the other declarations of the file.
No unpublished NYLL module is imported.

TaskHub tasks, the current Library, pending staging records and the pinned
Mathlib were searched by the original and adapted names. These bounded
searches found no existing declaration stating either target. Mathlib's
`isField_of_isIntegral_of_isField`
(`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`,
line 625), `IsDiscreteValuationRing.not_isField`
(`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`, line 70),
`integralClosure.isDedekindDomain`
(`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`, line 234) and
`IsDiscreteValuationRing.TFAE`
(`Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean`, line 210), together
with the published M245.006 localness theorem
`integralClosure_isLocalRing_of_finite_separable`, are tools for later
proofs, not proofs of these targets.

For provenance only: the original M245.010 proof uses the integrality of `B`
over `A`, the faithfulness of `B` over `A` from the source's M245.002
`CanonicalIntegralClosure.faithfulSMul` (lines 51–59, itself stated without
finite dimensionality), Mathlib's `isField_of_isIntegral_of_isField` to deduce
that `A` would be a field, and `IsDiscreteValuationRing.not_isField` for `A`.
The original M245.011 proof obtains `IsLocalRing B` from M245.006, the fraction
field property of `A` in `K` from the source's
`base_valuationSubring_isFractionRing` (`IntegralClosure.lean` line 472), the
Dedekind and Noetherian properties of `B` from Mathlib's integral-closure
results, `¬ IsField B` from M245.010, and concludes through
`IsDiscreteValuationRing.TFAE`. No original proof is included in, or claimed
as an implemented proof by, this statement module.

## Scope

This unit contains only these two statements. It does not state or prove the
other declarations of FiniteIntegralClosure.lean, including the M245.001 and
M245.002 wrappers, the M245.003–M245.006 completeness, Henselian, fiber and
localness results, the M245.007 maximal-ideal data, the M245.008 and M245.009
statements about the extended base maximal ideal, or the ideal-power,
valuation existence, uniqueness and completeness results from M245.012 on.
It makes no claim about complete local field packaging, residue actions,
inertia or reciprocity, and adds no global instance, theorem or public data
alias.

## Source record and attribution

The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its local source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The original file's SHA256 is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`. The
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`; it has
no source-specific entry for FiniteIntegralClosure.lean, so no further
third-party attribution applies. The published source partition
`notes/reuse/nyll-public-port/m241-m258.md` records no patch for M245
(`none in patch10`), and no applicable erratum was found in the project or
the published NYLL notes at extraction time.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, authors Naganori Yamaguchi (assisted by OpenAI Codex),
released under Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany the extraction and
match the pinned originals byte for byte.

Worker 764 extracted the two original theorem signatures on
30 October 2026, closed their quantifiers inside Prop-valued definitions with
explicit independent universe parameters, kept the source's `omit` of finite
dimensionality for M245.010 only, added the namespace prefix and target
names, unfolded the source abbreviation `base.valuationSubring`, reworded the
M245.010 docstring to match its actual hypotheses, reduced the imports to the
published `CompleteDVF` definition and the six Mathlib modules above, and
wrote this Markdown. The Lean header records these modifications. No other
worker's adapted Lean content was used. The module targets approved Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
