# Integral local tensor comparison: statement targets

This module imports `Langlands.Global.AdelicFunctoriality.IntegralTensorMaps`.
It defines two proposition targets in the namespace
`Langlands.Global.AdelicFunctoriality`:

- `IntegralLocalTensorComparison`, the main target;
- `IntegralTensorTransportBijective`, a separate supporting target.

The module proves nothing, and neither proposition is a hypothesis of the
other. Both quantify over number fields `K : Type u` and `L : Type v`, with
independent universe parameters, the hypotheses
`[Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]`, and an
arbitrary finite place `p : HeightOneSpectrum (𝓞 K)`. These are the field,
number-field and algebra hypotheses of `CompletedTensorComparison` in
`NormStatement`. There is no other premise: no Galois or abelian condition, no
comparison map or embedding given as data, and no injectivity, surjectivity or
coherence assumption.

Notation in this document:

- `O_p = p.adicCompletionIntegers K` and `K_p = p.adicCompletion K`;
- `L_q = q.1.adicCompletion L` and `O_q = q.1.adicCompletionIntegers L` for
  `q : FinitePlacesAbove L p`;
- `i_p = integralTensorInclusion L p`, `T_p = integralTensorComparison L p`
  and `τ_p = integralTensorTransport L p`.

These three maps are the published definitions of `IntegralTensorMaps`, used by
their Lean names. This module does not redefine them or add another map.

## The maps and their scalar structures

The maps are

```
i_p : 𝓞 L ⊗[𝓞 K] O_p →ₗ[𝓞 L] 𝓞 L ⊗[𝓞 K] K_p,          b ⊗ x ↦ b ⊗ (x : K_p),
T_p : 𝓞 L ⊗[𝓞 K] K_p →ₗ[𝓞 L] ((q : FinitePlacesAbove L p) → L_q),
      (b ⊗ x) q = algebraMap (𝓞 L) L_q b * FiniteExtension.completionMap p q.1 x,
τ_p : 𝓞 L ⊗[𝓞 K] K_p →ₐ[𝓞 K] K_p ⊗[K] L,                b ⊗ x ↦ x ⊗ algebraMap (𝓞 L) L b.
```

The formulas are the published lemmas `integralTensorInclusion_tmul`,
`integralTensorComparison_tmul` and `integralTensorTransport_tmul`.

The coefficient structures are as follows.

- In `𝓞 L ⊗[𝓞 K] O_p`, the ring `𝓞 K` acts on `O_p` by Mathlib's instance in
  `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean`.
- In `𝓞 L ⊗[𝓞 K] K_p`, the ring `𝓞 K` acts on the `K`-algebra `K_p` by
  restriction of scalars along `𝓞 K → K`. This is Mathlib's ring-of-integers
  instance.
- In both tensor products, `𝓞 L` acts on the left factor. This is the module
  structure for which `i_p` and `T_p` are `𝓞 L`-linear.
- Each `L_q` is an `𝓞 L`-algebra by restriction from `L`. `T_p` uses the
  completion map `K_p → L_q` of the scoped `FiniteExtension` algebra. This map
  is the continuous extension of `K → L → L_q`.
- `K_p ⊗[K] L` is the domain of the published `finiteTensorMap p`. Here `K`
  acts on `K_p` and on `L` through their given `K`-algebra structures. `τ_p` is
  only an `𝓞 K`-algebra map.

`IntegralTensorMaps` records the compatibility of the two actions of `𝓞 K`
with two scoped `IsScalarTower` instances. These instances are `Prop`-valued,
and the definitions of the three maps already use them. The statements below
mention only the maps, their ranges and coerced sets of completed integers.
They need no scalar instance beyond those fixed by the types of the maps. The
module therefore does not open the `FiniteExtension` scope.

## Main target `IntegralLocalTensorComparison`

For all `K`, `L` and `p` as above, the proposition is the conjunction of three
clauses.

1. `Function.Bijective (integralTensorComparison L p)`.
2. `Set.range (integralTensorComparison L p ∘ integralTensorInclusion L p) =
   Set.pi Set.univ (fun q : FinitePlacesAbove L p =>
   (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L)))`.
3. `Set.BijOn (integralTensorComparison L p)
   (Set.range (integralTensorInclusion L p)) (Set.pi Set.univ ...)`, with the
   same product set as in clause 2.

Clause 1 says that `T_p` is bijective. Since `T_p` is `𝓞 L`-linear, this gives
an `𝓞 L`-linear equivalence `𝓞 L ⊗[𝓞 K] K_p ≃ Π_q L_q` whose underlying function
is the canonical map `T_p`. An arbitrary equivalence would not suffice.

Clause 2 identifies the image of the integral tensor product. The composite
`T_p ∘ i_p` sends `b ⊗ x`, for `b : 𝓞 L` and `x : O_p`, to the family
`q ↦ algebraMap (𝓞 L) L_q b * completionIntegersMap p q.1 x`
(published lemma `integralTensorComparison_integralTensorInclusion_tmul`).
The clause says that the range of this composite is exactly the set of
families whose coordinate at every `q` lies in `O_q`. By `Set.range_comp`,
this range is `T_p '' Set.range i_p`.

Clause 3 is the `Set.BijOn` form that the downstream consumer uses. Its source
set is `Set.range i_p`, a subset of `𝓞 L ⊗[𝓞 K] K_p`. The clause does not
identify `𝓞 L ⊗[𝓞 K] O_p` with that subset, and no clause asserts that `i_p` is
injective. Clause 3 follows from clauses 1 and 2: injectivity of `T_p` gives
injectivity on the subset, and clause 2 gives `T_p '' Set.range i_p` equal to
the product. It is stated so that the consumer does not need to derive it.

`FinitePlacesAbove L p` is the Library index
`{q : HeightOneSpectrum (𝓞 L) // q.asIdeal.LiesOver p.asIdeal}`, defined in
`Norm`. It is finite by the published instance `finitePlacesAbove_finite`. The
target uses this actual index, not an arbitrary finite type. Imperial indexes
the places above `p` by `Extension B v = {w // w.under A = v}`. The published
equivalence `finitePlacesAboveEquiv L p` matches the two indices without
changing the underlying prime.

## Supporting target `IntegralTensorTransportBijective`

For all `K`, `L` and `p` as above, the proposition is
`Function.Bijective (integralTensorTransport L p)`. That is, the transport
`τ_p : 𝓞 L ⊗[𝓞 K] K_p → K_p ⊗[K] L`, `b ⊗ x ↦ x ⊗ algebraMap (𝓞 L) L b`, is
bijective. The map changes the coefficient ring from `𝓞 K` to `K` and the
first factor from `𝓞 L` to `L`. It also swaps the order of the two tensor
factors.

Mathematically, `L` is the localization of `𝓞 L` at the nonzero elements of
`𝓞 K`, and `K_p` is a `K`-module. Hence
`𝓞 L ⊗[𝓞 K] K_p ≅ L ⊗[K] K_p ≅ K_p ⊗[K] L`. This module states only the
specialization to number fields and to the module `K_p`. It adds no general
transport definition, and it proves nothing.

## Correspondence with Imperial FLT

The source is ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`. Imperial works with general data
`A, K, L, B`. Here these are `𝓞 K, K, L, 𝓞 L`, and `v` is `p`.

- `FLT/DedekindDomain/Completion/BaseChange.lean:810–821`. These lines define
  `integerBaseChangeLinearEquiv : B ⊗[A] K_v ≃ₗ[B] Π (w : Extension B v), L_w`
  and its lemma `integerBaseChangeLinearEquiv_tmul_apply`. The value on
  `b ⊗ x` is `algebraMap B L_w b * algebraMap K_v L_w x`. Imperial constructs it
  as `(linearEquivTensorProductModuleLeft A K L B K_v).symm`, followed by its
  field comparison `baseChangeAlgEquiv`. `T_p` has the same pure-tensor formula,
  with Imperial's completion algebra replaced by `completionMap`. Imperial's
  "this is a linear equivalence" is clause 1, stated for the canonical map.
- Lines 533–547 of the same file:
  `range_baseChange_comp_tensorAdicCompletionTo_eq_pi`. It states
  `Set.range (baseChange K L B v ∘ tensorAdicCompletionIntegersTo K L B v) =
  Set.univ.pi (fun w ↦ (w.1.adicCompletionIntegers L).carrier)`. Imperial's
  composite `B ⊗[A] O_v → L ⊗[K] K_v → Π_w L_w` sends `b ⊗ x` to
  `algebraMap L L_w (algebraMap B L b) * algebraMap K_v L_w x`
  (`tensorAdicCompletionIntegersTo_tmul` at lines 370–376 and
  `baseChange_tmul_apply` at lines 263–264). This is the value of `T_p ∘ i_p`.
  The two composites have the same domain and are additive, so they agree as
  maps. Imperial's range theorem is therefore clause 2 for the Library's
  factorization through `𝓞 L ⊗[𝓞 K] K_p`, after reindexing by
  `finitePlacesAboveEquiv`. The carrier of a valuation subring is the coerced
  set used here.
- Lines 854–870 of the same file: `integerBaseChangeLinearEquiv_bijOn`. Its
  source set is `Set.range (adicCompletionIntegers.tensorCoe K B v)`, and
  `tensorCoe` (lines 836–844) is the source of `i_p`. Its target set is
  `Submodule.pi Set.univ (fun w ↦ integerSubmodule L w.1)`. The carrier of
  that submodule is the set of families with every coordinate in `O_w`
  (`integerSubmodule`, lines 823–826). So clause 3 is this theorem with the
  equivalence replaced by its underlying canonical map `T_p`. Imperial proves
  it from the equivalence and the range theorem with `Equiv.bijOn_image`. This
  is the same derivation of clause 3 from clauses 1 and 2 described above.
- Lines 364–376 of the same file: `tensorAdicCompletionIntegersTo`, the
  integral map into `L ⊗[K] K_v`. The Library instead factors through
  `i_p : 𝓞 L ⊗[𝓞 K] O_p → 𝓞 L ⊗[𝓞 K] K_p`, as explained above.
- Lines 549–572 of the same file: `Extension.adicCompletionIntegersRingHom` and
  the `O_v`-algebra structures on `O_w` and `L_w`. The Library already has
  `FiniteExtension.completionIntegersMap`, which appears in the formula for
  `T_p ∘ i_p`. This module adds no such algebra.
- Lines 574–591 of the same file: the `IsBiscalar B O_v` instance for
  `tensorAdicCompletionIntegersTo`, the tower `IsScalarTower O_v K_v L_w`, and
  the `O_v`-algebra map `tensorAdicCompletionIntegersToPiRight`. These give the
  integral composite its second, `O_v`-linear structure. The targets here
  concern only the underlying functions, ranges and bijectivity. So they need
  no `O_v`-linear structure, and this module adds none.
- `FLT/DedekindDomain/IntegralClosure.lean:207–297`: `LinearEquivTensorProduct`
  (`L ≃ₗ[K] K ⊗[A] B`), `linearEquivTensorProductModule` and
  `linearEquivTensorProductModuleLeft` (`L ⊗[K] M ≃ₗ[B] B ⊗[A] M` for a
  `K`-module `M`), with their pure-tensor lemmas. By
  `linearEquivTensorProductModuleLeft_symm_tmul` (lines 291–293), the inverse
  for `M = K_v` sends `b ⊗ x` to `algebraMap B L b ⊗ x`. Following it with
  `TensorProduct.comm` gives `x ⊗ algebraMap B L b`, which is the value of
  `τ_p`. So `IntegralTensorTransportBijective` is the bijectivity part of
  Imperial's equivalence, restated for the canonical transport. Imperial's
  proof uses `IsLocalization.leftModuleTensorEquiv` from its own
  `FLT/Mathlib` directory. Project Mathlib has only
  `IsLocalization.moduleTensorEquiv` and `IsLocalization.moduleLid`
  (`Mathlib/RingTheory/Localization/BaseChange.lean`). Nothing is ported here.

Imperial's final section assumes `[FiniteDimensional K L]` and
`[Module.Finite A B]`. For number fields, instance search finds
`FiniteDimensional K L` and `Module.Finite (𝓞 K) (𝓞 L)`. This was checked by a
private development check. The targets therefore take no finiteness
hypothesis.

## Intended later proofs

This module proves neither target. The intended routes, for separate proof
tasks, are as follows.

- Supporting target: a localization argument for the specialization above,
  using the Mathlib interfaces just named. Its proof is a separate task.
- Clause 1: the published theorem `finiteTensorMap_integralTensorTransport`
  gives `finiteTensorMap p ∘ τ_p = T_p` as functions. The published theorem
  `completedTensorComparison` gives bijectivity of `finiteTensorMap p`.
  Bijectivity of `τ_p` then gives clause 1. So the main target's proof needs the
  supporting target, but the main proposition does not assume it.
- Clause 2: the integral range theorem. Imperial proves it by a topological
  closure argument (`Completion/BaseChange.lean:378–547`).
- Clause 3: from clauses 1 and 2, as explained above.

## Provenance and modification notice

Both targets restate conclusions of the Imperial theorems and definitions cited
above. The source is retained in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`ImperialCollegeLondon--FLT/source`. Both source files have the header
"Copyright (c) 2025 Kevin Buzzard", with authors Kevin Buzzard, Andrew Yang and
Matthew Jasper, under Apache-2.0. The Lean file keeps that header and adds a
modification notice. The upstream root `LICENSE` is retained at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).

Worker 382 made these modifications:

- the general Dedekind data are specialized to number fields in independent
  universes;
- `Extension` is replaced by the Library's `FinitePlacesAbove`;
- Imperial's linear equivalences are replaced by the Library's canonical maps
  `T_p` and `τ_p`, with bijectivity stated as a proposition;
- Imperial's integral composite through `L ⊗[K] K_v` is replaced by the
  composite `T_p ∘ i_p` through `𝓞 L ⊗[𝓞 K] K_p`, and its submodule target by
  the coerced set product;
- the separate transport target and the explicit three-clause form are derived
  for the Library interface.

No Lean proof, external import or Anthropic code is used. None of the audit's
compatibility patches (a)–(d) applies, because no source is ported. The public
audit [finite-adele base change](../../../notes/reuse/finite-adele-base-change-audit.md)
explains the reuse boundary.

## Checks

A private development check compiled the module without errors or warnings.
Inspection of `IntegralLocalTensorComparison` and of
`IntegralTensorTransportBijective` reported `Prop`-valued definitions with
universe parameters `u` and `v`. Each depends only on `propext`,
`Classical.choice` and `Quot.sound`. These checks are not independent semantic
acceptance.
