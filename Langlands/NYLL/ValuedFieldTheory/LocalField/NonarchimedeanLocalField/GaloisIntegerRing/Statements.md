# Integer-ring restriction evaluation statements

This module defines exactly two closed propositions in
`Langlands.NYLL.LocalFieldTheory`, adapting the types of NYLL source units
M139.003 and M139.004. They specify the ambient-field evaluations of the
published `galoisGroupIntegerRingEquivOfIsIntegralClosure` and its inverse.
The module supplies statement targets; it proves neither proposition.

## Complete targets

The first declaration is
`Langlands.NYLL.LocalFieldTheory.GaloisGroupIntegerRingEquivOfIsIntegralClosureApplyStatement`.
It has type `Prop`, with one arbitrary universe parameter `u` and no
mathematical declaration parameters. Its entire body is:

```lean
∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝒪[L]),
  ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x : 𝒪[L]) : L) =
    σ (x : L)
```

The second declaration is
`Langlands.NYLL.LocalFieldTheory.GaloisGroupIntegerRingEquivOfIsIntegralClosureSymmApplyStatement`.
It likewise has type `Prop`, one arbitrary universe parameter `u`, and no
mathematical declaration parameters. Its entire body is:

```lean
∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝒪[L]),
  (((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).symm x : 𝒪[L]) : L) =
    σ.symm (x : L)
```

Thus the first formula evaluates the forward ring equivalence and the
second evaluates the inverse of that same ring equivalence. The equality
in each formula is oriented from the coerced integer-ring value to the
corresponding field-automorphism value.

## Hypotheses, concrete rings, and scalar structures

The fields `K` and `L` share the arbitrary universe `u`, as in the original
source. All fields, instances, the automorphism, and the integer-ring
element are universally quantified inside each proposition. Neither target
is specialized to `Type 0`.

With `open scoped ValuativeRel`, the notation `𝒪[F]` means the actual
Mathlib valuation integer ring
`Valuation.integer (ValuativeRel.valuation F)`. Its elements are the
elements of `F` whose valuation is at most one. The coercions to `L` in
the conclusions are the concrete subtype inclusions. The notation
`Gal(L/K)` denotes `K`-algebra automorphisms of `L` and does not assume
that the extension is Galois.

The supplied `Algebra K L` is the field algebra structure. The valuation
extension instance states that the valuation on `K` is equivalent to the
pullback of the valuation on `L`. Mathlib's canonical valuation-extension
instances induce the algebra structure of `𝒪[L]` over `𝒪[K]`; its
algebra map is the restriction of `algebraMap K L`. The canonical
algebra map `𝒪[L] → L` is the subtype inclusion, and the scalar towers
are precisely those inferred in the published definition. This module
installs no scalar or action instances.

The relative `IsIntegralClosure 𝒪[L] 𝒪[K] L` instance says that the
embedded integer ring of `L` is the integral closure of the integer ring
of `K` in `L`. These are exactly the original hypotheses. Neither target
adds algebraicity, finite-dimensionality, `IsGalois`, topology,
completeness, local-field, discreteness, prime, or a supplied preservation
certificate.

## Source correspondence and proof boundary

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The full source file has SHA-256
`5f84d148f49ea9a28bdcbd07b7d16e902ab47b6f47f37a88347848801bbb14b3`.
Lines 1–91 were read in full, including the imports and context,
preservation theorem, restriction definition, both evaluation laws and
their proofs.

| Partition unit | Original declaration in `LocalFieldTheory` | Original lines | Closed target in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M139.003 | `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply` | 70–78 | `GaloisGroupIntegerRingEquivOfIsIntegralClosureApplyStatement` |
| M139.004 | `galoisGroupIntegerRingEquivOfIsIntegralClosure_symm_apply` | 83–91 | `GaloisGroupIntegerRingEquivOfIsIntegralClosureSymmApplyStatement` |

The [public declaration partition](../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m139)
provides these source unit identifiers. Its `.END` dependencies are
conservative scheduling markers; this statement pair needs only the
published restriction definition, rather than the original module's
unrelated import closure.

Both original lemmas carry `@[simp]` and have proof `rfl`, because the
original ring equivalence uses subtype constructors with field values
`σ (x : L)` and `σ.symm (x : L)`. The
[published adapted definition](Definitions.md) instead packages
Mathlib's `galRestrict'` for `σ.toAlgHom` and `σ.symm.toAlgHom` using
`AlgEquiv.ofAlgHom`, then takes `toRingEquiv`.
Its restriction uses `IsIntegralClosure.equiv`, so the corresponding
evaluation route is propositional through Mathlib's
`algebraMap_galRestrict'_apply`, for the forward and inverse homomorphisms
respectively. This unit does not claim that the original `rfl` proof
survives, and exports no proof or simplification theorem.

The sole explicit import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Definitions`.
M139.005's automorphism-group homomorphism, M139.006's action, and later
integer-ring or residue-field actions are outside this unit. No inertia,
host local-field adapter, or reciprocity conclusion is asserted.

## Provenance, license, and modifications

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum file for either registration was found in the
project or current Library notes. The public partition records no
patch10 modification to this source module; no patch10 code is reused.

The original copyright and author header is retained verbatim in the
Lean file: copyright 2026 Naganori Yamaguchi, all rights reserved; authors
Naganori Yamaguchi (assisted by OpenAI Codex). The existing Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged
in the Library. Their SHA-256 values are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The NOTICE has no entry specific to `GaloisIntegerRing.lean`.

Worker 599 extracted the two theorem types, added the namespace prefix,
renamed them to the two PascalCase statement targets, moved every
mathematical parameter inside its proposition, retained a shared arbitrary
universe, removed proofs and simp attributes, reduced imports to the
published definition, and wrote this documentation on 26 October 2026.
No other worker contributed an adapted draft to this pair. The already
published definition and Mathlib are reused by import and declaration
name; their implementations are not copied here.
