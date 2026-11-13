# NYLL M139-integral-closure-actions: data

The actual group homomorphism from the group of K-algebra automorphisms of L to ring automorphisms of its canonical valuation integer ring, followed by the induced multiplicative semiring action. The fields share an arbitrary universe and the only hypotheses beyond their field, valuation and algebra structures are valuation extension and the integral-closure property. No finite-dimensionality or Galois-extension assumption is required.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean`.
The original file SHA-256 is `5f84d148f49ea9a28bdcbd07b7d16e902ab47b6f47f37a88347848801bbb14b3`.
The readable original is retained under registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original name | Source declaration lines | Adapted name |
| --- | --- | --- | --- |
| M139.005 | `LocalFieldTheory.galoisGroupIntegerRingEquivHomOfIsIntegralClosure` | 95–108 | `Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivHomOfIsIntegralClosure` |
| M139.006 | `LocalFieldTheory.galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure` | 113–120 | `Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure` |

## Complete data and context

The Lean module has the following complete context and data. Its proof-field
adaptation to the published restriction is described below.

```lean
noncomputable section

universe u

open scoped ValuativeRel

/-- Real Galois automorphisms act on `𝒪[L]` through the actual integral-closure
restriction. -/
def galoisGroupIntegerRingEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝒪[L] ≃+* 𝒪[L]) where
  toFun := galoisGroupIntegerRingEquivOfIsIntegralClosure K L
  map_one' := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L 1 x : 𝒪[L]) : L) =
      (x : L)
    rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
    rfl
  map_mul' := by
    intro σ τ
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L (σ * τ) x : 𝒪[L]) : L) =
      ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L τ x) : 𝒪[L]) : L)
    rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply,
      galoisGroupIntegerRingEquivOfIsIntegralClosure_apply,
      galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
    rfl

/-- The semiring action on the valuation integer ring induced by the actual
integral-closure restriction of `Gal(L / K)`. -/
@[reducible]
def galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulSemiringAction (Gal(L / K)) 𝒪[L] :=
  MulSemiringAction.compHom 𝒪[L] (galoisGroupIntegerRingEquivHomOfIsIntegralClosure K L)


end
```

## Adaptation and reuse

Worker 202 prefixed the source namespace with `Langlands.NYLL`, retained the
original declaration names, and reduced the import closure to:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs`
- `Mathlib.Algebra.Ring.Action.Basic`

The complete telescopes, original docstrings, homomorphism `toFun`, and
the complete action body are retained. The source `@[reducible]` attribute on
the action is retained; both declarations remain definitions, not instances.
The action body is exactly
`MulSemiringAction.compHom 𝒪[L] (galoisGroupIntegerRingEquivHomOfIsIntegralClosure K L)`.

The source M139.002 restriction is reused by its published exact name
`Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure`
from the companion `Definitions` module. That published definition implements
the actual restriction with Mathlib's `galRestrict'`, rather than the source
subtype constructor. Consequently the source `ext x; rfl` proof fields of
M139.005 cannot be retained verbatim. The two proof fields here first apply
`RingEquiv.ext` and `Subtype.ext`, then rewrite the ambient-field value with
the published theorem
`Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply`
from `Proofs`, and close the field automorphism identity by `rfl`.
The multiplication field uses this evaluation theorem for the product and
for the two component restrictions. This changes only the certificates:
the actual map into ring automorphisms and the induced action construction
are the source constructions on the published restriction.

The relevant source context is lines 20–26. Mathlib's `RingEquiv` multiplication
is composition, as is the multiplication on `Gal(L / K)`. Therefore the
homomorphism law retains the source order, with `σ * τ` acting as `σ` after
`τ`. The action is supplied as data and is installed only if a consumer
chooses it locally. No substitute module or unlisted unpublished prerequisite
is needed.

The Library and Mathlib were searched for these exact data declarations before
authoring. Related canonical Mathlib structures are reused directly through the
listed imports. This module introduces no global instance and copies no other
worker's draft.

## Attribution and scope

The original copyright and author header is retained verbatim. The Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain in the Library, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The public partition reports no patch10 modification for this module.
This supporting data asserts no host reciprocity, Tate, cup-product, transfer
or class-formation result.
