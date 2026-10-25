# Integral tensor transport: bijectivity

The theorem
`Langlands.Global.AdelicFunctoriality.integralTensorTransportBijective`
proves exactly the published proposition
`Langlands.Global.AdelicFunctoriality.IntegralTensorTransportBijective`.
Import `Langlands.Global.AdelicFunctoriality.IntegralTensorTransportProof`.

The proposition quantifies over `K : Type u` and `L : Type v`, independently,
with `[Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]`,
and every `p : HeightOneSpectrum (𝓞 K)`. Its conclusion is
`Function.Bijective (integralTensorTransport L p)`. The theorem has no
additional premise or parameter.

Write `A = 𝓞 K`, `B = 𝓞 L`, and `M = p.adicCompletion K`. The actual map is

```
integralTensorTransport L p : B ⊗[A] M →ₐ[A] M ⊗[K] L,
                              b ⊗ x ↦ x ⊗ algebraMap B L b.
```

The proof imports the published target and its canonical map without changing
either. It proves no integral-range assertion, comparison with a product of
completions, global adelic equivalence, topology statement, or norm result.

## Implemented proof

All intermediate equivalences and their evaluation lemmas are private. They
support this theorem without introducing a general localization API.

First, Mathlib's `IsIntegralClosure.isLocalization A K L B` identifies `L`
as the localization of `B` at the image of `nonZeroDivisors A`. Its hypotheses
are supplied by the number-field instances: `K` is the fraction field of `A`,
`B` is the integral closure of `A` in `L`, and `L/K` is algebraic. In the
domain `A`, the non-zero-divisors are exactly the nonzero elements.
The algebra structures and scalar towers are the existing ones on number
fields and their rings of integers.

The module-localization instance for
`(IsScalarTower.toAlgHom A B L).toLinearMap` then gives
`IsLocalizedModule.isBaseChange (nonZeroDivisors A) K`. Its equivalence
defines `integralFieldTensorEquiv`:

```
g : K ⊗[A] B ≃ₗ[K] L.
```

`IsBaseChange.equiv_tmul` proves the needed evaluation
`g (1 ⊗ b) = algebraMap B L b`. No denominator choices or new inverse
assumptions are supplied by this module.

The private `integralTransportEquiv` composes the following `A`-linear
equivalences:

```
B ⊗[A] M
  ≃ B ⊗[A] (K ⊗[A] M)
  ≃ (B ⊗[A] K) ⊗[A] M
  ≃ L ⊗[A] M
  ≃ L ⊗[K] M
  ≃ M ⊗[K] L.
```

The first step tensors the identity of `B` with the inverse of
`IsLocalization.moduleLid`; it sends `b ⊗ x` to `b ⊗ (1 ⊗ x)`.
The second is inverse tensor associativity. The third tensors the composite
`B ⊗[A] K ≃ K ⊗[A] B ≃ L`, using commutativity and `g`, with the identity
of `M`. The fourth is the inverse of `IsLocalization.moduleTensorEquiv`.
The last swaps the two factors over `K`.

Here `M` is the given `K`-module, and its `A`-action is the existing
ring-of-integers action restricted from `K`. Both `L` and `M` have the
existing `A`–`K` scalar towers. The `K`-linear equivalences are restricted
to `A` where required. This construction needs only `A`-linearity; it
introduces no new algebra instance on a completion or tensor product.

The lemma `integralTransportEquiv_tmul` evaluates the composite as
`b ⊗ x ↦ x ⊗ algebraMap B L b`. Its proof unfolds `moduleLid`,
`moduleTensorEquiv`, and `TensorProduct.equivOfCompatibleSMul`, then uses
the tensor evaluation lemmas and `g (1 ⊗ b) = algebraMap B L b`.

Finally, tensor induction compares the equivalence with
`integralTensorTransport L p`: the pure-tensor case is the two evaluation
formulas, and the addition case uses additivity. Function extensionality
gives equality of the underlying functions. Rewriting by this equality
transfers the equivalence's bijectivity to the exact canonical map.

## Provenance and modifications

Worker 50 adapted the localization argument from ImperialCollegeLondon/FLT,
commit `923d45174c500aa1d994ba973bac38ea39eacbf7`,
`FLT/DedekindDomain/IntegralClosure.lean:207–297`, in particular
`LinearEquivTensorProduct`, `linearEquivTensorProductModule`, and their
inverse pure-tensor formulas. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `ImperialCollegeLondon--FLT/source`.

The source's copyright is © 2025 Kevin Buzzard, with authors Kevin Buzzard,
Andrew Yang, and Matthew Jasper. Its Apache-2.0 header is retained in the
Lean file, together with a modification notice. The upstream license is at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
No Anthropic code or external repository import is used.

The changes beyond the public audit's compatibility patches are explicit:

- Specialize the general Dedekind-domain and module construction to number
  fields in independent universes and the actual completion `M`.
- Replace the upstream construction through `LocalizedModule.iso` and
  `LocalizedModule.equivTensorProduct` by Mathlib's
  `IsLocalizedModule.isBaseChange` and `IsBaseChange.equiv`.
- Use the inverse of the `A`-linear chain and append tensor commutativity;
  omit the upstream `B`-linear generalization and its absent
  `leftModuleTensorEquiv` interface.
- Prove the pure-tensor identity by unfolding Mathlib's existing equivalences.
  The upstream simplification identities in
  `FLT/Mathlib/RingTheory/Localization/BaseChange.lean:29–40` were consulted,
  but no additional public simplification lemma or module is ported.
- Identify the constructed equivalence with the Library's canonical map and
  prove the published universal proposition.

The audit's patches (a)–(d) concern other files and are not needed here.
The relevant audit is
[Finite-adele base change](../../../notes/reuse/finite-adele-base-change-audit.md).
Worker 52 supplied the focused task specification; this proof was written by
Worker 50 and reuses no unpublished worker draft.

## Development validation

The prepared Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment compiled the module
without errors or warnings. Declaration inspection found a theorem with
universe parameters `u` and `v`, depending only on `propext`,
`Classical.choice`, and `Quot.sound`. These development checks do not replace
independent semantic review, exact-target validation, or publication.
