# NYLL M140: integer-unit evaluation and equivariance targets

These are proposition definitions for evaluation of the actual integer-unit
action and equivariance of the actual inclusion from integer units to field
units. Both retain every source hypothesis, the shared arbitrary universe,
explicit `K L`, the explicit automorphism and unit arguments, and the complete
source order. Each source local action `let` is retained in the proposition.
No finite-dimensionality or Galois-extension hypothesis is added.

Worker 230 extracted the two statements, changed `theorem name : P := by ...`
to `def nameStatement : Prop := P`, and omitted the proofs. The source `simp`
attribute on M140.004 is omitted because the new declaration defines a
proposition. The namespace is prefixed with `Langlands.NYLL`. The imports
are reduced to the companion `Valuation.IntegerDefinitions` and
`Valuation.Definitions` modules under
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation`.
The opened namespaces are adjusted to the published names.

The integer action is the companion M140.003 definition; the field-unit action
is M140.001 in `Valuation.Definitions`. The actual restriction is the published
`Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure`.
The actual monoid homomorphism `integerUnitsToFieldUnits` is reused from
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`, imported through
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`.
No data constructor, proof substitute or global instance is added. These
propositions are targets for later proofs.

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

| Unit | Original name | Source statement lines | Adapted name |
| --- | --- | --- | --- |
| M140.004 | `LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul` | 64–73 | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smulStatement` |
| M140.007 | `LocalClassFieldTheory.integerUnitsToFieldUnits_galoisGroup_equivariant` | 102–113 | `Langlands.NYLL.LocalClassFieldTheory.integerUnitsToFieldUnits_galoisGroup_equivariantStatement` |

## Complete Lean context and declarations

```lean
open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

def galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smulStatement
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[L]ˣ) : Prop :=
    let _ : MulDistribMulAction (Gal(L / K)) 𝒪[L]ˣ :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    σ • x = Units.mapEquiv
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv x

def integerUnitsToFieldUnits_galoisGroup_equivariantStatement
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[L]ˣ) : Prop :=
    let _ : MulDistribMulAction (Gal(L / K)) 𝒪[L]ˣ :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    let _ : MulDistribMulAction (Gal(L / K)) Lˣ :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    integerUnitsToFieldUnits L (σ • x) =
      σ • integerUnitsToFieldUnits L x
```

## Attribution and scope

The original copyright and author header is retained verbatim. The modification
header names Worker 230 and describes the extraction, namespace and import
changes. The published `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
are retained. These units introduce no global instances and prove no host
class-formation, reciprocity, Tate, transfer or cup-product target.
