# NYLL M142.001: actual valuation short-exactness target

The proposition states the five source properties of the actual valuation
sequence: equivariance of the inclusion of integer units into field units,
equivariance of the multiplicative valuation, the description of its kernel
by integer units, injectivity of the inclusion and surjectivity of the
valuation. The local actions are the actual integral-closure action on integer
units, the canonical field-unit action and the trivial value-group action.
The target does not assert a Herbrand quotient formula.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ValuationHerbrand.lean`,
context lines 34–41 and statement lines 44–58. Original file SHA-256:
`fc840414815c6b092d5cbc41cfb13cde82fee786a59ee24fbe46f66126a6b89d`.
The retained original is in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` and the path above.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original name | Adapted name |
| --- | --- | --- |
| M142.001 | `LocalClassFieldTheory.valuationHerbrand_shortExact` | `Langlands.NYLL.LocalClassFieldTheory.valuationHerbrand_shortExactStatement` |

## Complete Lean context and target

Both fields have type `Type` in universe zero, exactly as in this source
module. The source variable telescope and its `omit [FiniteDimensional K L]`
are preserved below. Thus the target requires no finite-dimensionality
instance. It does require all listed valuation, topology, local-field,
algebra, valuation-extension and integral-closure instances, in source order.
No Galois-extension hypothesis is present. The three source `letI` action
bindings and the order of the five conjuncts are unchanged.

```lean
open Langlands.NYLL.LocalFieldTheory

noncomputable section

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure (ValuativeRel.valuation L).integer
    (ValuativeRel.valuation K).integer L]

omit [FiniteDimensional K L] in
def valuationHerbrand_shortExactStatement : Prop :=
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    letI := galoisGroupValueGroupMulDistribMulAction K L
    (∀ (σ : Gal(L / K)) (x : (ValuativeRel.valuation L).integerˣ),
        integerUnitsToFieldUnits L (σ • x) =
          σ • integerUnitsToFieldUnits L x) ∧
      (∀ (σ : Gal(L / K)) (x : Lˣ),
        valuationUnitsMulHom L (σ • x) =
          σ • valuationUnitsMulHom L x) ∧
      (∀ x : Lˣ, valuationUnitsMulHom L x = 1 ↔
        ∃ y : (ValuativeRel.valuation L).integerˣ,
          integerUnitsToFieldUnits L y = x) ∧
      Function.Injective (integerUnitsToFieldUnits L) ∧
      Function.Surjective (valuationUnitsMulHom L)
```

## Modification record and reuse

Worker 230 extracted M142.001 and prefixed the namespace with `Langlands.NYLL`.
The source theorem and proof become a definition with the `Statement` suffix
and body equal to the source proposition. The proof is omitted; no proof
substitute is supplied. Unused `CyclicCohomology` and `Herbrand` opens are
omitted because the proposition uses no cohomology object.
The source module docstring is replaced by the precise description above.

The imports are reduced to the following published dependency and companion
action modules:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions`
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Definitions`
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`

The first two modules supply M140.003, M140.001 and M140.005. The actual maps
`integerUnitsToFieldUnits` and `valuationUnitsMulHom` are reused by their
names in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`.
The former is defined in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`
and the latter in the imported `ValuationExactSequence.Definitions`.
Only these data definitions are needed by this statement; no theorem proof
or unlisted source prerequisite is copied.

## Attribution and scope

The original copyright and author header is retained verbatim, with an
explicit modification header. The published `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained. The module introduces no global instance.
This is a proposition target for a separate proof; it discharges no host
class-formation, Herbrand, reciprocity, Tate, cup-product or transfer target.
