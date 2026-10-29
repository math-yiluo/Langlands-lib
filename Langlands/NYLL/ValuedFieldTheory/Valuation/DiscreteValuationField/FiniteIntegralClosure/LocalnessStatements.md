# Fiber uniqueness and localness of finite integral closures

This module defines exactly two closed proposition targets corresponding to
two theorems of Naganori Yamaguchi's NYLL ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, both in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`:

- M245.005,
  [lines 117–174](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean#L117-L174);
- M245.006,
  [lines 176–251](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean#L176-L251).

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
| `ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_base_maximal_fiber_subsingleton_of_finite_separable` | `IntegralClosureBaseMaximalFiberSubsingletonOfFiniteSeparableStatement.{u, v, w}` | M245.005; `universe u v w` at line 23, ambient variables at 30–31, docstring 117–121, signature 122–127, proof through 174 |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_isLocalRing_of_finite_separable` | `IntegralClosureIsLocalRingOfFiniteSeparableStatement.{u, v, w}` | M245.006; same universe line and ambient variables, docstring 176–182, signature 183–186, proof through 251 |

The spelling map adds the `Langlands.NYLL` namespace prefix, converts each
theorem name to PascalCase
(`integralClosure_base_maximal_fiber_subsingleton_of_finite_separable` becomes
`IntegralClosureBaseMaximalFiberSubsingletonOfFiniteSeparable`, and
`integralClosure_isLocalRing_of_finite_separable` becomes
`IntegralClosureIsLocalRingOfFiniteSeparable`) and appends `Statement`. Only
universe levels are declaration parameters: each complete, unapplied constant
has type `Prop`, with universe parameters `u, v, w` in that order.

## Quantifiers

Both bodies universally quantify, in order:
`(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] (base : CompleteDVF.{u, v} K)
[Algebra.IsSeparable K L]`.
These are the source's ambient variables of lines 30–31 followed by the two
binders of each theorem's own signature, in the source order. The
`omit [FiniteDimensional K L]` directives of the source file apply only to
other declarations (M245.001, M245.002 and later units); both selected
theorems keep finite dimensionality. The source binds `K` and `L` implicitly
and `base` explicitly; inside a universally quantified proposition the
explicit binders used here state the same mathematics, and the
instance-implicit binders are the source's.

`CompleteDVF.{u, v} K` is the published structure from
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`
(source unit M107.006): a value group `ValueGroup : Type v` with a
`LinearOrderedCommGroupWithZero` structure, a valuation
`valuation : Valuation K ValueGroup`, and an instance
`Valuation.IsCompleteDiscrete valuation`, which says that the valuation is
rank-one discrete and that its valuation subring is adically complete for
its maximal ideal. It is used unchanged.

## Unfolding of the source abbreviations

The source signatures write `base.valuationSubring` and `base.maximalIdeal`.
In the source these are abbreviations along the path
`CompleteDVF → HenselianDVF → DVF`:

- `CompleteDVF.valuationSubring F := F.toHenselianDVF.valuationSubring`
  (`Complete.lean` line 133), `HenselianDVF.valuationSubring F :=
  F.toDVF.valuationSubring` (`Henselian.lean` line 202) and
  `DVF.valuationSubring F := F.valuation.valuationSubring` (`Basic.lean`
  line 54), where `toHenselianDVF` builds its DVF with
  `valuation := F.valuation` (`Complete.lean` lines 118–121). So
  `base.valuationSubring` is the subtype `↥base.valuation.valuationSubring` of
  Mathlib's `Valuation.valuationSubring`.
- `CompleteDVF.maximalIdeal F := F.toHenselianDVF.maximalIdeal`
  (`Complete.lean` line 137), `HenselianDVF.maximalIdeal F :=
  F.toDVF.maximalIdeal` (`Henselian.lean` line 206) and
  `DVF.maximalIdeal F := IsLocalRing.maximalIdeal F.valuationSubring`
  (`Basic.lean` line 73). So `base.maximalIdeal` is
  `IsLocalRing.maximalIdeal ↥base.valuation.valuationSubring`.

The targets write these terms directly, as the task requires. Writing
`A := ↥base.valuation.valuationSubring`,
`m := IsLocalRing.maximalIdeal A` and `B := integralClosure A L`, the first
body concludes `Subsingleton (PrimeSpectrum (m.Fiber B))` and the second
concludes `IsLocalRing B`; the Lean bodies spell out `A`, `m` and `B` in full
rather than using `let` binders.

The source's ring structures on the valuation subring are Mathlib's: its
instance `DVF.valuationSubring.commRing` is
`ValuationSubring.instCommRingSubtypeMem` and its instance
`DVF.valuationSubring.isLocalRing` is `ValuationSubring.isLocalRing`
(`Basic.lean` lines 58–66). In the targets Lean synthesizes exactly these two
Mathlib instances for `A`, so `m` is the maximal ideal for the same local
ring structure.

The published module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`
contains adapted aliases `CompleteDVF.valuationSubring` and
`CompleteDVF.maximalIdeal`. A private development check confirmed that
`base.valuationSubring = ↥base.valuation.valuationSubring`,
`HEq base.maximalIdeal (IsLocalRing.maximalIdeal ↥base.valuation.valuationSubring)`
and `integralClosure base.valuationSubring L =
integralClosure ↥base.valuation.valuationSubring L` all hold by
`with_reducible rfl`. This module does not import that alias module, so the
targets do not depend on it, and it adds no alias of its own.

## Scalar structures, integral closure and residue fiber

- `Algebra A L` is Mathlib's `Algebra.ofSubsemiring` instance for the
  subring `A` of `K` (`Mathlib/Algebra/Algebra/Basic.lean`, line 101). Its
  algebra map is `(algebraMap K L).comp (algebraMap A K)`: the inclusion of
  `A` into `K` followed by the structure map `K → L`. A development check
  confirmed this equality by `rfl`.
- `integralClosure A L` is Mathlib's `integralClosure`
  (`Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`, line 216): the
  `A`-subalgebra of `L` whose elements are the elements of `L` integral over
  `A`. `B` is its coercion to a type, with the commutative ring structure
  `Subalgebra.toCommRing` and the `A`-algebra structure `Subalgebra.algebra`
  restricted from `L`. Nothing about `B` is assumed beyond this definition.
- `m.Fiber B` is Mathlib's `Ideal.Fiber`
  (`Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean`, lines 62–67), the
  abbreviation `m.ResidueField ⊗[A] B`; a development check confirmed this
  unfolding by `rfl`. Here `Ideal.ResidueField m`
  (`Mathlib/RingTheory/LocalRing/ResidueField/Ideal.lean`, lines 28–34) is
  `IsLocalRing.ResidueField (Localization.AtPrime m)`, the residue field of
  the localization of `A` at `m`. Because `A` is already local, it is
  canonically isomorphic to the residue field `A ⧸ m`, but it is not
  definitionally that quotient. The primality instance that `Ideal.Fiber`
  requires is synthesized as `Ideal.IsMaximal.isPrime'` from the maximality
  of `m`. The fiber is this actual tensor product, not a separately chosen
  ring or a residue field of a chosen extension valuation.
- `PrimeSpectrum R` (`Mathlib/RingTheory/Spectrum/Prime/Defs.lean`, lines
  28–36) is the type of prime ideals of a commutative ring `R`.
- `IsLocalRing R` (`Mathlib/RingTheory/LocalRing/Defs.lean`, lines 27–34) says
  that `R` is nontrivial and that whenever `a + b = 1`, `a` or `b` is a unit;
  for a commutative ring this means that `R` has exactly one maximal ideal.

## Mathematical meaning

`IntegralClosureBaseMaximalFiberSubsingletonOfFiniteSeparableStatement` says:
for every field `K` with a chosen complete discrete valuation `base`, with
valuation ring `A` and maximal ideal `m`, and every finite separable field
extension `L` of `K`, the fiber `κ(m) ⊗[A] B` of the integral closure `B` of
`A` in `L` has at most one prime ideal. It asserts no existence of a prime and
does not name a chosen prime. Through Mathlib's
`PrimeSpectrum.primesOverOrderIsoFiber` (`Fiber.lean` line 196) the
primes of this fiber correspond to the primes of `B` lying over `m`; the
target states only the fiber form, as the source does.

`IntegralClosureIsLocalRingOfFiniteSeparableStatement` says: for the same
data, the integral closure `B` of `A` in `L` is a local ring. It does not take
the first target as a premise.

Neither body adds `Module.Finite A B`, a `HenselianRing` or `IsAdicComplete`
hypothesis on `B`, an Artinian or subsingleton fiber, `IsLocalRing B`,
`IsIntegralClosure` of an assumed valuation ring, a chosen extension
valuation, `Valuation.HasExtension`, residue-field finiteness, a topology, an
extension record or any other conclusion-like premise. The completeness of
the base enters only through the `CompleteDVF` structure.

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
- `Mathlib.FieldTheory.Separable`, providing `Algebra.IsSeparable`;
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, providing
  `FiniteDimensional`;
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, providing
  `integralClosure`;
- `Mathlib.RingTheory.LocalRing.Defs`, providing `IsLocalRing`;
- `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`, providing `Ideal.Fiber`
  together with `Ideal.ResidueField` and the tensor product;
- `Mathlib.RingTheory.Spectrum.Prime.Defs`, providing `PrimeSpectrum`.

The source file imports
`Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core`
and `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`; these
are needed only by the omitted proofs and the other declarations of the file.
No unpublished NYLL module is imported.

TaskHub tasks, the current Library and the pinned Mathlib were searched by the
original and adapted names and for localness or fiber-subsingleton results on
integral closures. These bounded searches found no existing declaration
stating either target. Mathlib's
`PrimeSpectrum.primesOverOrderIsoFiber`,
`Ideal.exists_maximal_ideal_liesOver_of_isIntegral` and
`IsLocalRing.of_singleton_maximalSpectrum`
(`Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`, line 66) are tools
for later proofs, not proofs of these targets.

For provenance only: the original M245.005 proof makes `B` a finite
`A`-module through `IsIntegralClosure.finite`, deduces that the fiber is
Artinian, and shows that its idempotents are trivial by lifting them along
the surjection `B → m.Fiber B`, using the Henselian property of `B` from
M245.004, the source's idempotent-lift helper M104.004 in `Henselian.lean`
and the fact that `B` is a domain. The source's generic fiber helpers
M192.001–.003 in `IntegralClosure.lean` supply the surjectivity and kernel of
`B → m.Fiber B` and the step from trivial idempotents of an Artinian ring to
at most one prime. The original M245.006
proof uses integrality and M245.002 to find a maximal ideal of `B` over `m`,
M245.005 with `PrimeSpectrum.primesOverOrderIsoFiber` to make it the only
prime over `m`, contraction of maximal ideals under the integral extension
to show that every maximal ideal of `B` lies over `m`, and finally
`IsLocalRing.of_singleton_maximalSpectrum`. No original proof is included in,
or claimed as an implemented proof by, this statement module.

## Scope

This unit contains only these two statements. It does not state or prove the
other declarations of FiniteIntegralClosure.lean, including the M245.001 and
M245.002 wrappers, the M245.003 and M245.004 completeness and Henselian
statements, the M245.007 maximal-ideal data or the later discrete valuation
ring, valuation existence or uniqueness results. It makes no claim about
complete local field packaging, residue actions, inertia or reciprocity, and
adds no global instance or public data alias.

## Source record and attribution

The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its local source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The original file's SHA256 is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`. The
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`; its
ValuedFieldTheory third-party source table does not list
FiniteIntegralClosure.lean, so no further third-party attribution applies.
The published source partition `notes/reuse/nyll-public-port/m241-m258.md`
records no patch for M245 (`none in patch10`), and no applicable erratum was
found in the project or the published NYLL notes at extraction time.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, authors Naganori Yamaguchi (assisted by OpenAI Codex),
released under Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany the extraction and
match the pinned originals byte for byte.

Worker 764 extracted the two original theorem signatures on
28 October 2026, closed their quantifiers inside Prop-valued definitions with
explicit independent universe parameters, added the namespace prefix and
target names, unfolded the source abbreviations `base.valuationSubring` and
`base.maximalIdeal`, reduced the imports to the published `CompleteDVF`
definition and the six Mathlib modules above, and wrote this Markdown. The
Lean header records these modifications. No other worker's adapted Lean
content was used. The module targets approved Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
