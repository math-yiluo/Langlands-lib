# Identification and calculation of the actual cocharacter reflex field

Author: Worker 57.

This module identifies the fixed field of the actual first-factor Kottwitz
scheme-cocharacter conjugacy class with the previously constructed real Hodge
reflex field. It then transfers the published numerical field calculations and
constructs the same scheme-cocharacter field directly from Harris signature
and CM-section hypotheses.

## Inputs and internal provenance

The central-simple unitary datum is `D : CentralSimpleUnitaryData E K A n`.
The number field `E` is totally real, `K` is totally complex and quadratic over
`E`, and the algebra structures and the `E/K/A`, `ℚ/E/A` and `ℚ/K/A` scalar
towers are those in the Lean declarations. The charts
`C : HarrisSignatureCharts D.toSecondKindInvolution n Φ` retain the signature,
center action and matrix comparisons of the existing construction. The
comparison requires `hΦ : IsCMSection E K Φ`.

This is an internal derivation from
[CocharacterFixedField](CocharacterFixedField.md),
[CocharacterReflexProof](CocharacterReflexProof.md), and the imported
[RealReflex](RealReflex.md) calculations. The first module defines the actual
scheme-cocharacter stabilizer and its intermediate fixed field in `ℂ/ℚ`.
The second proves the stabilizer membership equivalence without assuming
scheme conjugacy from scalar evaluations. The numerical formulas and their
source conventions remain those documented in `RealReflex` and
[Reflex](Reflex.md). No additional external theorem or source assertion is used.

## Subgroup and fixed-field equalities

`kottwitzCocharacterStabilizer_eq` proves equality of the actual subgroups

```text
D.complexCocharacterStabilizer (D.kottwitzCocharacter C true)
  = hodgeStabilizer (D.realHodgeFunction C).
```

Subgroup extensionality reduces this to membership for each rational algebra
automorphism of `ℂ`. That equivalence is precisely the published
`complexCocharacterReflexStabilizer D C hΦ`.

`kottwitzCocharacterReflexField_eq_realReflexField` applies the fixed-field
construction to this subgroup equality. It identifies
`D.kottwitzCocharacterReflexField C` with `D.realReflexField C` as intermediate
fields, rather than merely giving an abstract field isomorphism.
`kottwitzCocharacterReflexField_eq_reflexField` then uses the published real
field comparison to identify this field with `C.reflexField`.

## Construction from signature hypotheses

`kottwitzCocharacterReflexFieldOfSignature` takes
`h : HasHarrisSignature D.toSecondKindInvolution n` and
`hΦ : IsCMSection E K Φ`. It obtains the charts with
`HarrisSignatureCharts.ofSignature h hΦ` and takes the fixed field of the
resulting actual scheme-cocharacter class. No arbitrary output field or
cocharacter is supplied. The theorem
`kottwitzCocharacterReflexFieldOfSignature_eq` identifies this construction
with `D.realReflexFieldOfSignature h hΦ`, using the same constructed charts.

## Field calculations

`kottwitzCocharacterReflexField_eq_bot` retains `hΦ`, assumes `n = 2` and
`Subsingleton (E →+* ℝ)`, and proves that the actual cocharacter field is `⊥`,
the image of `ℚ` in `ℂ`. Its proof rewrites to the real reflex field and
applies `realReflexField_eq_bot`.

For the Harris section, take a CM number field `F` quadratic over `ℚ`,
`j : F →+* K` and `τ₀ : F →+* ℂ`, with charts for
`harrisCMSection E j τ₀`. The theorem
`kottwitzCocharacterReflexField_eq_distinguishedImage` assumes
`3 ≤ n ∨ ∃ τ, τ ≠ CH.distinguished`. It proves equality with
`CH.distinguishedImage`, the image of the full CM center `K` in `ℂ` under the
distinguished embedding. The proof obtains the CM-section condition from
`isCMSection_harrisCMSection`, rewrites by the field comparison, and applies
the published real reflex-field calculation. There is no extra fixed-field
or Galois correspondence hypothesis.

These results identify and calculate the field of the actual cocharacter
class. They do not construct a canonical model or prove descent of a Shimura
variety, PEL representability, scheme level towers or coefficient descent.
