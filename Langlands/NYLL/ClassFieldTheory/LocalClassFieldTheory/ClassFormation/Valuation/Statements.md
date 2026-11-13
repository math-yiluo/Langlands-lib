# Valuation invariance, kernel and surjectivity targets

This pair extracts six source theorem statements as `Prop`-valued definitions.
All adapted declarations lie in `Langlands.NYLL.LocalClassFieldTheory`.
The common original prefix is `LocalClassFieldTheory.`; each adapted name
appends `Statement` to the original basename and adds `Langlands.NYLL.`.

| Unit | Original basename | Source declaration and statement lines | Source proof extent |
| --- | --- | --- | --- |
| M140.006 | `galoisGroupValueGroupMulDistribMulAction_smul` | 92–97 | 97–99 |
| M140.008 | `valuationMap_unitsMapEquiv_galoisGroup` | 122–131 | 131–185 |
| M140.009 | `valuationUnitsMulHom_galoisGroup_equivariant` | 189–201 | 201–204 |
| M140.010 | `valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero` | 208–212 | 212–220 |
| M140.011 | `valuationUnitsMulHom_eq_one_iff_exists_integerUnit` | 224–228 | 228–237 |
| M140.013 | `valuationUnitsMulHom_surjective` | 253–256 | 256–262 |

## Exact interfaces and meaning

M140.006 keeps `(K L : Type u) [Field K] [Field L] [Algebra K L]`
then `(σ : Gal(L/K)) (n : Multiplicative Int)`. Its body is the source
`let _ : MulDistribMulAction (Gal(L / K)) (Multiplicative Int) :=
galoisGroupValueGroupMulDistribMulAction K L; σ • n = n`.
The local action is part of the proposition, not an extra instance argument.

M140.008 keeps, in order, `(K L : Type u) [Field K] [ValuativeRel K]`,
`[Field L] [ValuativeRel L] [TopologicalSpace L]`,
`[IsNonarchimedeanLocalField L] [Algebra K L]`,
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`,
`[IsIntegralClosure 𝒪[L] 𝒪[K] L]`, then `(σ : Gal(L/K)) (x : Lˣ)`.
Its body is exactly
`valuationMap L (Additive.ofMul (Units.mapEquiv σ.toMulEquiv x)) =
valuationMap L (Additive.ofMul x)`.
Only `L` is required to be a local field; no topology on `K`, finite-dimensionality,
or Galois-extension premise is inserted. The integral-closure premise stays
present even though the predicate does not computationally depend on it.

M140.009 keeps exactly the telescope of M140.008, and its body installs,
in order, the source field-unit action and the trivial value-group action as
local `let` instances. It asserts
`valuationUnitsMulHom L (σ • x) = σ • valuationUnitsMulHom L x`.
It needs no integer-unit action in its statement.

The last three targets keep `(L : Type u) [Field L] [ValuativeRel L]`
`[TopologicalSpace L] [IsNonarchimedeanLocalField L]` in that order.
M140.010 and .011 then take `(x : Lˣ)`. Their bodies respectively say
`valuationUnitsMulHom L x = 1 ↔ valuationMap L (Additive.ofMul x) = 0`
and `valuationUnitsMulHom L x = 1 ↔
∃ y : 𝒪[L]ˣ, integerUnitsToFieldUnits L y = x`.
M140.013 has no element binder and has body
`Function.Surjective (valuationUnitsMulHom L)`.
Each telescope uses the source arbitrary shared universe `u`.

All valuation and inclusion names denote published actual NYLL maps:
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationUnitsMulHom`
and `.valuationMap` from `ValuationExactSequence.Definitions`, and
`.integerUnitsToFieldUnits` from `Basic.U016.Definitions`.
The additive valuation retains NYLL's sign convention. The propositions keep
`Additive.ofMul`, `Units.mapEquiv`, the canonical valuation integer ring `𝒪[L]`,
and the exact multiplicative kernel and existential range condition.

## Modifications and validation

Each source `theorem ... : P := by ...` becomes `def ...Statement : Prop := P`.
No proof is included, assumed as a new axiom or smuggled into an argument.
The other changes are the namespace prefix, adjusted comments and reduced
imports. Opens are fully qualified to select the published NYLL valuation maps;
Mathlib supplies the canonical valuation-extension and integral-closure instances.
The file imports `Valuation.Definitions`, `ValuationExactSequence.Definitions`
and `Mathlib.RingTheory.Valuation.Extension`.

Source bodies are retained literally after the statement transformation. These
six targets require neither M139's new integer action nor the uniformizer
proofs used only by the source proof of M140.008. The unlisted source M140.002
and .012 are not required by the extracted statements and are not extracted.
The remaining M140.003,.004,.007 integer-action-dependent units belong to a separate pair.
This support layer discharges no host class-formation, Tate, cup, transfer or
reciprocity target. Proofs of these targets require separate proof tasks.

Development compilation in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
returned no diagnostics; focused inspection of
`Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_surjectiveStatement`
reported `statement_returns_prop: true`. Compilation is not independent acceptance.

## Source and attribution

The pinned original is Naganori Yamaguchi's NYLL project at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`
(file SHA-256 `478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`).
The complete source module, lines 1–265, was read. It is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`.

The registered sources are `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum appears in `notes/errata/`.
The original copyright and author header is preserved verbatim, including
Naganori Yamaguchi (assisted by OpenAI Codex). The original Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library.
Worker 230 made this extraction and wrote its documentation on 13 November 2026.
The source-to-port changes are recorded below. No source-specific NOTICE entry
is changed, and no Mathlib implementation is copied.
