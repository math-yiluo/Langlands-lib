# NYLL M140: integer-unit action data

The action of `Gal(L / K)` on the actual valuation integer units is induced
by the integral-closure restriction of the field automorphisms. The fields
share the arbitrary universe `u`; the full field, valuation, algebra, valuation
extension and integral-closure hypotheses occur in their source order below.
There is no finite-dimensionality or Galois-extension hypothesis.

The data body and `@[implicit_reducible]` attribute are unchanged. In particular,
`hIntegerAction` is the source local `MulSemiringAction`, and
`Units.mulDistribMulActionRight` lifts it to units. This definition is not
registered as a global instance.

Worker 230 extracted the declaration, prefixed the namespace with
`Langlands.NYLL`, and reduced imports to the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Actions`
and Mathlib's `Algebra.Group.Action.Units`. The source dependency
`LocalFieldTheory.galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure`
is reused by its published name with the `Langlands.NYLL` prefix; its body
uses the actual integral-closure restriction. No body or telescope change is
made here. The source docstring is shortened without changing its meaning.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`.
The retained file SHA-256 is
`478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`.
The original is readable in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` and the path above.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M140.003 | `LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure` | 49–60 (declaration 52–60) | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure` |

## Complete Lean context and declarations

```lean
open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The action on integer units induced by integral-closure restriction. -/
@[implicit_reducible]
def galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulDistribMulAction (Gal(L / K)) 𝒪[L]ˣ := by
  let hIntegerAction : MulSemiringAction (Gal(L / K)) 𝒪[L] :=
    galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  exact Units.mulDistribMulActionRight
```

## Attribution and scope

The original copyright and author header is retained verbatim. The modification
header names Worker 230 and describes the extraction, namespace and import
changes. The published `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
are retained. These units introduce no global instances and prove no host
class-formation, reciprocity, Tate, transfer or cup-product target.
