# Adic completeness under linear equivalence and for finite modules

This module defines exactly two closed proposition targets corresponding to
two theorems of Naganori Yamaguchi's NYLL ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`:

- M105.001 in
  [`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AdicPower.lean`, lines 22–52](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AdicPower.lean#L22-L52);
- M191.014 in
  [`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite.lean`, lines 257–275](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite.lean#L257-L275).

These definitions name propositions; they contain no proofs of the
propositions. Publishing them proves neither assertion. A subsequent proof
must establish each published target separately.

## Exact source correspondence

Both adapted names belong to
`Langlands.NYLL.ValuationTheory.DiscreteValuationField`. The source namespace
is `ValuationTheory.DiscreteValuationField`.

| Source theorem | Closed proposition target | Source unit and lines |
| --- | --- | --- |
| `ValuationTheory.DiscreteValuationField.isAdicComplete_of_linearEquiv` | `IsAdicCompleteOfLinearEquivStatement.{u, v, w}` | M105.001; ambient variables at AdicPower.lean 22–24, signature at 28–30, proof through 52 |
| `ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite` | `IsAdicCompleteOfModuleFiniteStatement.{u, v}` | M191.014; `universe u v` at HenselianFinite.lean 25, signature at 261–266, proof through 275 |

The spelling map adds the `Langlands.NYLL` namespace prefix, converts each
theorem name to PascalCase (`isAdicComplete_of_linearEquiv` becomes
`IsAdicCompleteOfLinearEquiv`, `isAdicComplete_of_moduleFinite` becomes
`IsAdicCompleteOfModuleFinite`) and appends `Statement`. Each original
theorem's complete parameter telescope, including the ambient `variable`
declarations it uses, is quantified inside the corresponding definition.
Only universe levels are declaration parameters: each complete, unapplied
constant has type `Prop`, with universe parameters `u, v, w` and `u, v`
respectively, in that order.

## Independent universes

The source states M105.001 under `variable {R : Type*}`, `{M : Type*}` and
`{N : Type*}` (AdicPower.lean 22–24), so the ring and both modules may lie in
three unrelated universes. `IsAdicCompleteOfLinearEquivStatement.{u, v, w}`
keeps this: `R : Type u`, `M : Type v` and `N : Type w`.

The source states M191.014 with `{R : Type u} {M : Type v}` (line 262), so the
ring and module universes are independent.
`IsAdicCompleteOfModuleFiniteStatement.{u, v}` keeps this: `R : Type u` and
`M : Type v`. Neither target restricts to a shared universe or to `Type 0`.

This matters because the approved Mathlib result that finite modules over a
Noetherian ring have tensor-product adic completions,
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, is stated in the
section `Noetherian` of `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean`
whose variables bind `R : Type u` and `M : Type u` in the same universe
(lines 218–219), despite `Type*` binders at the top of that file. The source's
same-universe theorem M191.013 (`isAdicComplete_of_moduleFinite_sameUniverse`,
HenselianFinite.lean 224–255) wraps that result. M191.014 is the
independent-universe generalization. M191.013 is deliberately not exposed as a
separate target; it is a special case of M191.014 (take `v = u`), and a later
proof may keep its own same-universe helper private.

## Quantifiers and mathematical meaning

`IsAdicCompleteOfLinearEquivStatement` universally quantifies, in order:
`(R : Type u) (M : Type v) (N : Type w) [CommRing R] [AddCommGroup M]
[Module R M] [AddCommGroup N] [Module R N] (I : Ideal R)
(_e : M ≃ₗ[R] N) [IsAdicComplete I M]`, and concludes `IsAdicComplete I N`.
It says: if `M` and `N` are modules over the same commutative ring `R`,
linearly equivalent over `R`, and `M` is `I`-adically complete, then `N` is
`I`-adically complete for the same ideal `I`. The equivalence is a hypothesis
whose existence is all the conclusion needs, so its binder carries the
`_e` spelling that silences Lean's unused-variable linter; the name has no
mathematical effect. No finite generation, Noetherianity, topology or other
hypothesis on `R`, `M` or `N` is added.

`IsAdicCompleteOfModuleFiniteStatement` universally quantifies, in order:
`(R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
(I : Ideal R) [IsNoetherianRing R] [Module.Finite R M]
[IsAdicComplete I R]`, and concludes `IsAdicComplete I M`.
It says: a finitely generated module over a Noetherian commutative ring that
is `I`-adically complete is itself `I`-adically complete. Here
`IsAdicComplete I R` uses the canonical module structure of `R` over itself.
No Henselian, field, discrete valuation, integral-closure, local-ring,
nontriviality, residue-cardinality, primality, selected completion or
conclusion-like premise is added, and `M` carries no topology or algebra
structure beyond the supplied additive group and module structure.

In both bodies `IsAdicComplete I X` is Mathlib's algebraic class from
`Mathlib/RingTheory/AdicCompletion/Basic.lean` (lines 45–56): it extends
`IsHausdorff I X` (the submodules `I ^ n • ⊤` intersect in zero) and
`IsPrecomplete I X` (every sequence that is Cauchy for the filtration
`I ^ n • ⊤` converges for it). It takes no topology argument.

The source binds the types `R`, `M`, `N` implicitly and `I`, `e` explicitly;
inside a universally quantified proposition the explicit binders used here
state the same mathematics, and the instance-implicit binders are the
source's. The binder order differs from the source only by moving
independent binders: the type variables come first in both targets, and in
the second target the ideal `I` follows the module structures instead of
preceding them (source lines 262–263). Reordering independent binders does not
change the proposition.

## Mathlib reuse and imports

The direct imports are:

- `Mathlib.RingTheory.AdicCompletion.Basic`, providing `IsAdicComplete`,
  together with `Ideal`, `Module` and `LinearEquiv` through its imports;
- `Mathlib.RingTheory.Finiteness.Defs`, providing `Module.Finite`;
- `Mathlib.RingTheory.Noetherian.Defs`, providing `IsNoetherianRing`.

No NYLL module is imported. The source imports of HenselianFinite.lean
(`Henselian`, `AdicPower`, `Mathlib.Algebra.Module.Shrink`,
`Mathlib.RingTheory.AdicCompletion.AsTensorProduct`,
`Mathlib.RingTheory.AdicCompletion.Noetherian`, `Mathlib.RingTheory.Nakayama`)
and AdicPower.lean's `Mathlib.RingTheory.AdicCompletion.Functoriality` are
needed only by the omitted proofs.

The current Library and the pinned Mathlib were searched by the original and
adapted names and for `IsAdicComplete` together with `LinearEquiv` or
`Module.Finite`. Neither contains a general transport of `IsAdicComplete`
along a linear equivalence or a finite-module completeness theorem.
Mathlib's related results are `AdicCompletion.of_bijective_iff`
(completeness as bijectivity of the canonical map), the same-universe
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`,
`IsAdicComplete.map_algebraMap_iff` in `AdicCompletion/Basic.lean` and
`IsAdicComplete.congr_ringEquiv` in `AdicCompletion/Topology.lean`. These are
tools for later proofs, not proofs of these targets. The last two cover the
source's mapped-ideal and ring-equivalence lemmas M105.006 and M105.007, so no
duplicate targets for those units are introduced here.

For provenance only: the original M105.001 proof shows bijectivity of
`AdicCompletion.of I N` by conjugating with `AdicCompletion.congr I e`; the
original M191.014 proof uses `Module.Finite.small` and `Shrink.linearEquiv`
to move `M` into universe `u`, applies M191.013 there, and transports
completeness back with M105.001. No original proof is included or claimed as
an implemented proof by this statement module.

## Scope

This unit contains only these two statements. It does not state or prove the
other declarations of AdicPower.lean or HenselianFinite.lean, including the
linear-equivalence chain M191.001–M191.012, the same-universe M191.013, the
Henselian consequence M191.015 or anything later. It adds no global instance
and makes no claim about Henselian rings, finite integral closures, valuation
extensions, inertia or reciprocity.

## Source record and attribution

The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its local source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The original files' SHA256 values are
`df1f92c6b85a87ad4a27c319302f267a717b7f82c1cce10167c56b1c4793232d`
(AdicPower.lean) and
`ba8c98a9f27133d8ba9637baf667805e783a3999654b1711e5f72601e749aab1`
(HenselianFinite.lean). The attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`; its
ValuedFieldTheory third-party source table does not list either file, so no
further third-party attribution applies. No applicable erratum was found in
the project or the published NYLL notes at extraction time. The retained
feasibility patch P2 for HenselianFinite.lean changes only M191.004, and no
patch changes AdicPower.lean, so neither selected signature is affected.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, authors Naganori Yamaguchi (assisted by OpenAI Codex),
released under Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany the extraction and
match the pinned originals byte for byte.

Worker 785 extracted the two original theorem signatures on
27 October 2026, closed their quantifiers inside Prop-valued definitions with
explicit independent universe parameters, added the namespace prefix and
target names, reduced the imports to the three Mathlib modules above, and
wrote this Markdown. The Lean header records these modifications. No other
worker's adapted Lean content was used. The module targets approved Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
