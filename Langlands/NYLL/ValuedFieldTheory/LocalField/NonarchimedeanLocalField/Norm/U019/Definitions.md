# The field norm on valuation-ring units

This module adapts NYLL M129.019 and M129.022 as the data definitions
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue`
and
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnits`.
The namespace is inherited from the source; neither definition assumes that
either field is a local field.

With independent universes `u` and `v`, the complete telescopes are:

```lean
def normIntegerUnitsValue
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L]
    [Langlands.NYLL.LocalFieldTheory.ValuativeExtension K L]
    (x : 𝒪[L]ˣ) : 𝒪[K]

def normIntegerUnits
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [Langlands.NYLL.LocalFieldTheory.ValuativeExtension K L] :
    𝒪[L]ˣ →* 𝒪[K]ˣ
```

The notation `𝒪[K]` denotes the integer subring of
`ValuativeRel.valuation K`. The namespaced `ValuativeExtension K L`
is the published NYLL class asserting that every element of `𝒪[L]`, viewed
in `L`, is integral over `𝒪[K]`. It is distinct from Mathlib's root class
of the same short name, which compares valuative relations along an algebra
map. These definitions use only the namespaced integrality class. They assume
no topology, finite dimensionality, Galois condition, or comparison of the
two valuations.

The first definition returns the field norm `Algebra.norm K (x : L)` with
its proof of membership in `𝒪[K]`. The second returns that value as a unit:
its chosen inverse is the first definition applied to `x⁻¹`. Its underlying
field value is definitionally

```lean
(((normIntegerUnits K L x : 𝒪[K]ˣ) : 𝒪[K]) : K) =
  Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L)
```

It is a monoid homomorphism because the field norm preserves one and
multiplication. This supplies a restricted norm construction, with no
surjectivity or norm-index assertion.

## Source and changes

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean`.
The complete file was read; its SHA-256 is
`0e9e3d68b6d964addae89ea2185146fdee7c6b60bf23cfff679a20f34e808eb6`.
Its universe and section context is at lines 20–34 and 63–65.

| Unit | Original declaration | Adapted declaration |
| --- | --- | --- |
| M129.019, lines 172–176 | `LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue` |
| M129.022, lines 204–221 | `LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnits` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnits` |

The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
in its `n-yamaguchi-0729--ClassFieldTheory/source/` directory. The
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the published errata.

Worker 120 extracted these two definitions on 11 November 2026, added
the `Langlands.NYLL` namespace prefix, and replaced the original broad
imports with the published `ValuativeExtension.Definitions` module and
Mathlib's `RingTheory.Norm.Transitivity` and `RingTheory.Valuation.Integral`.
The original universes, binder visibility and order, hypotheses, values,
inverse values, and homomorphism laws are retained.

Two proof dependencies are supplied directly by existing declarations:

| Source dependency | Replacement used here |
| --- | --- |
| M129.009, `algebraNorm_mem_integers_of_mem_integers`, lines 101–107 | The published `Langlands.NYLL.LocalFieldTheory.ValuativeExtension.integer_isIntegral`, followed by Mathlib `Algebra.isIntegral_norm` and `Valuation.Integers.mem_of_integral` with `Valuation.integer.integers`. This is the original proof term, inserted at the membership field. |
| M129.020–021, `normIntegerUnitsValue_mul_inv` and `normIntegerUnitsValue_inv_mul`, lines 178–202 | Mathlib `mul_inv_cancel`, `inv_mul_cancel`, `congrArg`, `map_mul` and `map_one`. Their applications are inserted into the two inverse fields after subtype extensionality, following the original proofs. |

No separate theorem declaration is added for these helpers. The submitted
data therefore require neither their named NYLL theorems nor the other
preceding M129 commands. In particular, M129.018, the conservative
inventory predecessor of M129.019, is not an import dependency. The
source imports `NormUnits`, `ValuativeExtension` and `Basic` reduce here
to the published integrality interface; `NormUnits` and `Basic` are not
needed. No existing norm or valuation construction is duplicated, and
no instance is introduced.

## Checks

The initial focused build and the full source-comparison build passed
with no errors or warnings in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
A private probe reconstructed both original definitions and their helper
proofs in the complete source section. Definitional equality of each
whole constant with its adaptation passed, as did explicit checks of both
complete telescopes with independent universes and of the field-value
coercion. A further probe checked the exact M129.009 replacement under
its original hypotheses. Thus the reduced imports and the local proof
replacements suffice for these data definitions. These development
checks provide no independent acceptance or proof publication.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The original Apache-2.0 [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are already
published. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`;
both copies were checked against the original. The NOTICE has no
source-specific entry for this module. No patch10 code or another
worker's draft was reused.
