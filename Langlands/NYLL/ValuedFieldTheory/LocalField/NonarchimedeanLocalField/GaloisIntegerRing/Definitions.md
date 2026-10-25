# Galois restriction to an integral-closure valuation ring

The single definition
`Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure`
restricts a field automorphism to the actual canonical valuation integer ring.
It adapts unit M139.002 of the NYLL declaration partition, preserving its full
interface and changing its implementation to reuse Mathlib's generic integral-closure
restriction.

## Interface and meaning

The complete interface, with canonical inferred scalar structures, is:

```lean
(K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
[Algebra K L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
(σ : Gal(L/K)) : 𝒪[L] ≃+* 𝒪[L]
```

The universe `u` is arbitrary and shared by `K` and `L`, as in the source.
Here `Gal(L/K)` means the group of `K`-algebra automorphisms of `L`; this
notation does not assert that the extension is Galois. The scoped notation
`𝒪[F]` denotes `Valuation.integer (ValuativeRel.valuation F)`, whose elements
are the field elements with valuation at most one. The result is a ring
equivalence of this concrete subtype with itself.

The field algebra is the supplied `Algebra K L`. Integer-ring scalar
structures and both towers through `K` and through `𝒪[L]` are the existing
Mathlib structures, provided by valuation extension and scalar restriction.
In particular, `algebraMap 𝒪[L] L` is the subtype inclusion, and the map
`𝒪[K] → 𝒪[L]` is induced by `algebraMap K L`. No alternative algebra,
scalar-tower, or action instance is installed by this module.

The extension hypothesis says that the valuation of `K` is equivalent to
the pullback of the valuation of `L`. The integral-closure hypothesis says
that the embedded `𝒪[L]` is precisely the integral closure of `𝒪[K]` in `L`.
There are no additional algebraicity, finite-dimensionality, Galoisness,
topology, completeness, discrete-valuation, local-field, prime, or supplied
preservation-certificate hypotheses.

## Construction and evaluation

Let `f = galRestrict' 𝒪[K] 𝒪[L] 𝒪[L] σ.toAlgHom` and let `g` be the
same Mathlib construction applied to `σ.symm.toAlgHom`. These are
`𝒪[K]`-algebra endomorphisms of `𝒪[L]`. Mathlib's `galRestrict'_comp` and
`galRestrict'_id`, together with the inverse identities for `σ`, give
`f.comp g = AlgHom.id _ _` and `g.comp f = AlgHom.id _ _`.
`AlgEquiv.ofAlgHom` packages these two intrinsic inverse certificates,
and `toRingEquiv` gives the requested data.

Mathlib's `algebraMap_galRestrict'_apply` identifies the field value of the
forward map at `x : 𝒪[L]` with `σ (x : L)`. Applied to `σ.symm.toAlgHom`,
it identifies the field value of the inverse map with `σ.symm (x : L)`.
Thus this construction has the same actual forward and inverse actions as
the source. Mathlib's stronger `galRestrict` equivalence is not used:
its additional `Algebra.IsAlgebraic K L` hypothesis would strengthen this
interface unnecessarily.

The original implementation uses subtype constructors with those field
values and the source preservation theorem M139.001. Its evaluation lemmas
M139.003–004 therefore have proofs `rfl`. This implementation instead uses
`IsIntegralClosure.equiv` inside `galRestrict'`, so the field evaluation is
propositional rather than definitional. Both formulas were checked privately
using `algebraMap_galRestrict'_apply`; both corresponding `rfl` attempts fail.
These diagnostics are not exported theorem declarations. Public evaluation
statements and proofs remain separate units. M139.001 is neither imported
nor asserted to have been published.

The only explicit imports are:

- `Mathlib.RingTheory.IntegralClosure.IntegralRestrict`;
- `Mathlib.RingTheory.Valuation.Extension`;
- `Mathlib.Topology.Algebra.Valued.ValuativeRel`.

The third import supplies the canonical scoped integer-ring notation; it
adds no topological hypothesis to the declaration. The pair introduces no
automorphism-group homomorphism, action instance, ideal action, residue
action, host adapter, or standalone preservation theorem.

## Source correspondence and attribution

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean`, lines 52–65](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean#L52-L65),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Its file SHA-256 is
`5f84d148f49ea9a28bdcbd07b7d16e902ab47b6f47f37a88347848801bbb14b3`.
The source mapping is
`LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure` to
`Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure`.
Lines 1–130, including the preservation theorem at 34–48 and evaluation
lemmas at 70–91, were read for context. No other source unit is extracted.

The readable original belongs to registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the project or published notes. The
recorded patch10 does not modify this source module.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex). The original Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already retained in
the Library and are unchanged. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The NOTICE has no source-specific entry for `GaloisIntegerRing.lean`.

Worker 104 isolated the definition, added the namespace prefix, replaced
the original import closure with the three Mathlib imports, implemented
the generic restriction construction, and wrote this documentation on
25 October 2026. Worker 106 contributed the proposed `galRestrict'` and
`AlgEquiv.ofAlgHom` construction route. No source draft or patch10 code
was reused. Mathlib is reused by import and declaration name, without
copying its implementations.
