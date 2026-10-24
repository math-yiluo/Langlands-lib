# Canonical integral tensor maps at a finite place

This module imports `Langlands.Global.AdelicFunctoriality.Inclusion`. It defines
the canonical maps for the integral form of finite-adele base change at one
finite place, and it defines an index equivalence for the places above it. The
fields `K : Type u` and `L : Type v` have independent universes. The hypotheses
are `[Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]`, and
`p : HeightOneSpectrum (𝓞 K)` is an arbitrary finite place. In this document
write

- `O_p = p.adicCompletionIntegers K` and `K_p = p.adicCompletion K`;
- `L_q = q.1.adicCompletion L` for `q : FinitePlacesAbove L p`.

All declarations are in `Langlands.Global.AdelicFunctoriality`, except the two
scoped instances, which are in its sub-namespace `FiniteExtension`. The module
opens the existing scope `FiniteExtension`. Within that scope the existing
completion algebra `Algebra K_p L_q` is induced by
`FiniteExtension.completionMap p q.1`. The module also uses the existing
`IsScalarTower K K_p L_q`. It adds no completion algebra, integral algebra, or
global instance. Lean omits a section instance that a declaration does not use.
For example, `integralTensorInclusion_tmul` and `integralTensorTransport_tmul`
do not take `[NumberField L]`. The two index lemmas do not take
`[NumberField K]`. These omissions only make the lemmas more general.

## Scalar coherence

Let `X` be a field with `Algebra K X`. Mathlib's ring-of-integers file then
gives `Algebra (𝓞 K) X` by restriction of scalars. Instance search uses this
action of `𝓞 K` on `K_p` and on `L_q`. Mathlib's scalar towers for completions
are stated for other actions of `𝓞 K`. These are the actions defined in
`Mathlib/RingTheory/DedekindDomain/AdicValuation.lean`. Both actions are the
composite of the inclusion `𝓞 K → K` with the coefficient map. So they are
definitionally equal, but instance search does not identify them. Two scoped
`Prop` instances record the compatibility that is needed:

- `FiniteExtension.isScalarTower_ringOfIntegers_adicCompletionIntegers p :
  IsScalarTower (𝓞 K) O_p K_p`;
- `FiniteExtension.isScalarTower_ringOfIntegers_adicCompletion q :
  IsScalarTower (𝓞 K) (𝓞 L) (q.adicCompletion L)`, for every
  `q : HeightOneSpectrum (𝓞 L)`.

Each is proved by `IsScalarTower.of_algebraMap_eq` with `rfl` at every element.
They define no new action. They are scoped so that they agree with the existing
scoped completion structures. The Library's
`CompletedRamification` towers are over `O_p`. The tower in `Extension` is over
`K`. So these instances do not duplicate them.

## The integral tensor inclusion `i_p`

```
integralTensorInclusion L p :
  𝓞 L ⊗[𝓞 K] O_p →ₗ[𝓞 L] 𝓞 L ⊗[𝓞 K] K_p
```

is `TensorProduct.AlgebraTensorModule.lTensor (𝓞 L) (𝓞 L)` applied to the
`𝓞 K`-linear inclusion. This inclusion is the linear map of
`Algebra.algHom (𝓞 K) O_p K_p`, and it uses the first scalar-coherence instance.
`integralTensorInclusion_tmul` gives the defining formula

```
integralTensorInclusion L p (b ⊗ₜ[𝓞 K] x) = b ⊗ₜ[𝓞 K] (x : K_p),
```

and its proof is `rfl`. The module does not assert that `i_p` is injective. It
does not identify `𝓞 L ⊗[𝓞 K] O_p` with a subobject. Later image statements
must use `Set.range (integralTensorInclusion L p)`.

## The comparison `T_p`

For each `q : FinitePlacesAbove L p`, Mathlib's `Algebra.TensorProduct.lift`
combines two algebra maps:

- the structure map `Algebra.ofId (𝓞 L) L_q`;
- the existing scoped completion `K`-algebra map
  `Algebra.algHom K K_p L_q`, restricted to `𝓞 K`.

The images commute because `L_q` is commutative. The scalar tower that `lift`
needs is the second scalar-coherence instance. `AlgHom.pi` collects these maps
over all places above `p`:

```
integralTensorComparisonAlgHom L p :
  𝓞 L ⊗[𝓞 K] K_p →ₐ[𝓞 L] ((q : FinitePlacesAbove L p) → L_q).
```

Then `integralTensorComparison L p` is its underlying `𝓞 L`-linear map. This
map is `T_p`, and `integralTensorComparison_apply` identifies the two maps by
`rfl`. The defining coordinate formula is

```
integralTensorComparison L p (b ⊗ₜ[𝓞 K] x) q =
  algebraMap (𝓞 L) L_q b * FiniteExtension.completionMap p q.1 x.
```

This is `integralTensorComparison_tmul`. The same formula for the algebra map is
`integralTensorComparisonAlgHom_tmul`, and both proofs are `rfl`.
`integralTensorComparison_integralTensorInclusion_tmul` describes the composite
`T_p ∘ i_p` on a pure tensor `b ⊗ x` with `x : O_p`. Its `q` coordinate is

```
algebraMap (𝓞 L) L_q b * (FiniteExtension.completionIntegersMap p q.1 x : L_q).
```

This reuses the existing `completionIntegersMap`, and the proof is `rfl`. The
module does not claim that `T_p` is bijective. It also does not prove the
integral range theorem.

## Transport to `finiteTensorMap`

The transport

```
integralTensorTransport L p : 𝓞 L ⊗[𝓞 K] K_p →ₐ[𝓞 K] K_p ⊗[K] L
```

is `Algebra.TensorProduct.lift` of two maps:

- `b ↦ 1 ⊗ₜ algebraMap (𝓞 L) L b`, which is `includeRight` restricted to `𝓞 K`
  after `IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L`;
- `x ↦ x ⊗ₜ 1`, which is `includeLeft` over `K` restricted to `𝓞 K`.

The tower argument `IsScalarTower (𝓞 K) (𝓞 K) (K_p ⊗[K] L)` of `lift` is given
explicitly. It is proved by `IsScalarTower.of_algebraMap_eq` with `rfl`,
because the same instance diamond occurs here. This proof is local to the
definition. `integralTensorTransport_tmul` gives

```
integralTensorTransport L p (b ⊗ₜ[𝓞 K] x) = x ⊗ₜ[K] algebraMap (𝓞 L) L b.
```

Its proof unfolds the definition with `simp`. The image of `b ⊗ x` is the product
`(1 ⊗ algebraMap (𝓞 L) L b) * (x ⊗ 1)` of the two tensors.

`finiteTensorMap_integralTensorTransport` says that for every
`z : 𝓞 L ⊗[𝓞 K] K_p`,

```
finiteTensorMap p (integralTensorTransport L p z) = integralTensorComparison L p z.
```

So `T_p` is the composite of the transport with the existing `finiteTensorMap`.
The proof is by induction on `z` over pure tensors and sums. Sums follow from
additivity of both sides. For `b ⊗ x`, compare the two sides at each place `q`.
By `finiteTensorMap_tmul`, the left side is
`completionMap p q.1 x * algebraMap L L_q (algebraMap (𝓞 L) L b)`. By
`integralTensorComparison_tmul`, the right side is
`algebraMap (𝓞 L) L_q b * completionMap p q.1 x`. These are equal by
commutativity and by Mathlib's tower `IsScalarTower (𝓞 L) L L_q`.

The transport is only an `𝓞 K`-algebra map here. Its bijectivity is the
localization transport `𝓞 L ⊗[𝓞 K] K_p ≅ L ⊗[K] K_p` up to the order of the
tensor factors. That theorem is a separate obligation, and this module does not
prove it.

## Index equivalence

```
finitePlacesAboveEquiv L p :
  FinitePlacesAbove L p ≃ {q : HeightOneSpectrum (𝓞 L) // q.under (𝓞 K) = p}
```

sends `q` to `⟨q.1, finitePlacesAbove_under p q⟩`. The inverse sends a prime `q`
with `q.under (𝓞 K) = p` to `q` itself. Its `LiesOver` proof substitutes the
equation and uses the existing instance `liesOver_under`. Both inverse laws are
`rfl`, by subtype eta and proof irrelevance. The simp lemmas
`finitePlacesAboveEquiv_apply_coe` and `finitePlacesAboveEquiv_symm_apply_coe`
state that the underlying prime does not change. Imperial indexes places by the
subtype on the right, called `Extension`. This equivalence lets downstream
statements move between that index and the Library's `FinitePlacesAbove`. The
existing `finitePlacesAboveEquivPrimesOver` in `FiniteComparisonReduction` has a
different target, `p.asIdeal.primesOver`.

## Checks

A private development check compiled the module without errors or warnings. A
Lake build also succeeded. The definition `integralTensorComparison` and the theorem
`finiteTensorMap_integralTensorTransport` use only `propext`,
`Classical.choice` and `Quot.sound`. These checks are not
independent semantic acceptance.

## Provenance and modification notice

The source is ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`. It is retained in the registered
source `external-lean-reuse-snapshots-2026-10-21`, with fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under the
directory `ImperialCollegeLondon--FLT/source`. The adapted parts are listed
below.

- [`FLT/DedekindDomain/Completion/BaseChange.lean`, lines 836–844](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/Completion/BaseChange.lean#L836):
  `adicCompletionIntegers.tensorCoe` and `tensorCoe_tmul`. These give the
  construction of `i_p` with `AlgebraTensorModule.lTensor` and its `rfl`
  formula.
- Lines 810–821 of the same file: `integerBaseChangeLinearEquiv` and
  `integerBaseChangeLinearEquiv_tmul_apply`. These are the source of the
  pure-tensor formula of `T_p`. Imperial defines that map as an equivalence,
  built from its own field-level comparison. Here `T_p` is only a map, and it is
  built directly from the Library's `completionMap`.
- Lines 364–376 of the same file: `tensorAdicCompletionIntegersTo` and its
  `tmul` lemma. They provide the `Algebra.TensorProduct.lift` pattern
  (`includeRight.restrictScalars` composed with `IsScalarTower.toAlgHom`) used by
  `integralTensorTransport`.
- [`FLT/DedekindDomain/IntegralClosure.lean`, line 41](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/IntegralClosure.lean#L41):
  `Extension B v := {w // w.under A = v}`, the target of the index equivalence.
- Lines 256–297 of the same file: `linearEquivTensorProductModuleLeft` and its
  `tmul` lemmas. They motivate only the direction and formula of the transport.
  Their equivalence proof is not ported.

Both source files have the header "Copyright (c) 2025 Kevin Buzzard", with
authors Kevin Buzzard, Andrew Yang and Matthew Jasper. The Lean file keeps that
header and the Apache-2.0 notice. The upstream root `LICENSE` is retained
byte-for-byte at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot contains no `NOTICE` file.

Worker 230 made these modifications:

- general Dedekind data `A, K, L, B` are replaced by `𝓞 K, K, L, 𝓞 L` for
  number fields in independent universes;
- `Extension` is replaced by the Library's `FinitePlacesAbove`;
- the Library's `finiteTensorMap`, `completionMap`, `completionIntegersMap` and
  scoped `FiniteExtension` completion algebra are used, not Imperial's
  field-level comparison or its global completion instance;
- `T_p` is defined directly as a map, not as an equivalence;
- the transport, the theorem `finiteTensorMap_integralTensorTransport`, the
  index equivalence and the two scalar-coherence instances are derived additions
  for the Library interface. They are not copied external theorems, and their
  proofs are described above.

None of the audit's compatibility patches (a)–(d) is needed. No external import
closure or Anthropic code is used. The public audit
[finite-adele base change](../../../notes/reuse/finite-adele-base-change-audit.md)
explains the reuse boundary. Later phases cover the bijectivity of `T_p`, the
exact integral range theorem, the `BijOn` theorem, the final equivalence, and
the bijectivity of the transport.
