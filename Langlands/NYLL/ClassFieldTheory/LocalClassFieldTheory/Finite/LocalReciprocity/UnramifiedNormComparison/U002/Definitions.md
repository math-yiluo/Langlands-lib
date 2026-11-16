# The canonical map from the norm quotient to the valuation quotient

This module adapts NYLL M267.002 as
`Langlands.NYLL.LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient`.
For the source finite unramified Galois extension `L/K`, it is the
multiplicative homomorphism

```lean
NormQuotient K L →*
  Kˣ ⧸ unramifiedNormSubgroup K (Module.finrank K L)
```

The domain is the actual quotient of `Kˣ` by the range of the field-norm
homomorphism `normUnits K L`. The codomain divides by the subgroup whose
normalized valuations are divisible by `[L : K]`. The construction descends
the published projection `unramifiedNormClass K (Module.finrank K L)` through
`Langlands.NYLL.LocalFieldTheory.normQuotientLift`. Its kernel condition follows
from the published theorem
`Langlands.NYLL.LocalClassFieldTheory.localNormSubgroup_le_unramifiedNormSubgroup`
and the published criterion
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormClass_eq_one_iff_mem`.

## Parameters and scope

Both fields remain at `Type` (universe zero). The section telescope is copied
from source lines 34–44: each field has `Field`, `ValuativeRel`,
`TopologicalSpace`, and `IsNonarchimedeanLocalField` instances; the extension
has `Algebra K L`, `FiniteDimensional K L`, and `IsGalois K L`; the valuation
of `L` extends that of `K`; `𝒪[L]` is the integral closure of `𝒪[K]` in `L`
and is finite as a module over `𝒪[K]`; and the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L`
class holds. All fifteen source instance parameters are retained. No
replacement norm, supplied inclusion, additional instance, or narrower
local-field hypothesis is introduced.

## Construction and imports

The definition body is unchanged. For `x` in the actual norm subgroup,
`localNormSubgroup_le_unramifiedNormSubgroup K L hx` places it in the
valuation-divisibility subgroup. The published quotient criterion then
makes `unramifiedNormClass K (Module.finrank K L) x = 1`.
`MonoidHom.mem_ker` expresses that assertion as membership in the kernel,
and `normQuotientLift` gives the requested homomorphism.

The three explicit imports are the published adaptations of M267.001
(`UnramifiedNormComparison.U001.Proofs`), M266.017
(`UnramifiedNormSubgroup.U017.Proofs`), and M093.007
(`NormQuotient.U007.Definitions`). Their imports provide the actual norm
quotient, valuation subgroup and canonical projections. These declarations
are reused by Lean name. The broad source imports of `Main`,
`SeparableNormValuation`, `UnramifiedFrobenius`, and cardinal finiteness are
unnecessary for this focused construction.

## Source correspondence and modifications

Original declaration:
`LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient`, lines 61–72
(docstring at 61, definition at 62–72, telescope at 34–44) of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The whole source file has
SHA-256 `a955313b05e5cdeb8bd4e9c6c76e466c956fe7231bb6fd90f4945a57e564ad26`.
It is in registered source `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`.

Worker 205 made these modifications on 16 November 2026:

1. Prefix the source namespace with `Langlands.NYLL`.
2. Replace the source imports by the three published modules above.
3. Extract only M267.002, preserving its source telescope, name, docstring,
   result type and complete definition body. Omit the surrounding redundant
   `noncomputable section`; the definition remains `noncomputable`.
4. Add a focused module docstring and this explanation, and retain the
   original copyright and author header with the dated modification record.

The original Apache-2.0 license and attribution notices remain in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

## Development check

A focused Lean-service build in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` succeeded with zero errors and
warnings. Inspection reports a definition with no universe parameters and
only `propext`, `Classical.choice`, and `Quot.sound` as axioms. This verifies
that the smaller published import set supplies the construction.
