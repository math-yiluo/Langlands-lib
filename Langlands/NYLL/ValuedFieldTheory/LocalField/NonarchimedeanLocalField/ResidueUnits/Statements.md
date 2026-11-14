# Residue units and integer units modulo first principal units: targets (M137 statements)

These are unproved Prop-valued definitions of five source theorem statements
about the data of `ResidueUnits/Definitions.lean`. Each keeps every source
binder, its implicit, explicit or instance kind, and its order, and its value is
the original conclusion verbatim. No proof is submitted here; the proofs are
separate `lean.proof@1` work.

Every adapted name has prefix `Langlands.NYLL.LocalFieldTheory.`; each original
has prefix `LocalFieldTheory.`. The suffix gains `Statement`.

| Unit | Original suffix | Source lines (statement) | Adapted suffix |
| --- | --- | --- | --- |
| M137.012 | protected `IntegerUnitsModPrincipalUnits.inductionOn` | 105–111 | protected `IntegerUnitsModPrincipalUnits.inductionOnStatement` |
| M137.016 | `integerUnitsToResidueUnits_apply` | 140–146 | `integerUnitsToResidueUnits_applyStatement` |
| M137.017 | `mem_ker_integerUnitsToResidueUnits_iff` | 149–153 | `mem_ker_integerUnitsToResidueUnits_iffStatement` |
| M137.018 | `principalUnits_one_eq_ker_integerUnitsToResidueUnits` | 165–168 | `principalUnits_one_eq_ker_integerUnitsToResidueUnitsStatement` |
| M137.022 | `integerUnitsToResidueUnits_surjective` | 208–210 | `integerUnitsToResidueUnits_surjectiveStatement` |

The line ranges run from each docstring to the end of the statement; the source
proofs (lines 112–115, 147, 154–163, 169–174 and 211–212) are omitted.

## The targets

Throughout, `K : Type u` carries `[Field K] [ValuativeRel K]` and nothing else;
`𝒪[K]`, `𝓀[K]` and `𝓂[K]` are Mathlib's valuation ring, residue field and
maximal ideal of `ValuativeRel.valuation K`.

- **M137.012.** Binders `{K : Type u} [Field K] [ValuativeRel K]`,
  `{motive : IntegerUnitsModPrincipalUnits K → Prop}`,
  `(q : IntegerUnitsModPrincipalUnits K)` and
  `(h : ∀ x : 𝒪[K]ˣ, motive (integerUnitsModPrincipalUnitsMk K x))`, in this
  order. The value is exactly `motive q`; the premise `h` stays a parameter
  and is not turned into an implication. The declaration is `protected`, as in
  the source. Because `h` does not occur in the value, the declaration is
  preceded by `set_option linter.unusedVariables false in`, which only silences
  that linter.
- **M137.016.** Binders `(K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ)`.
  The value is
  `((residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K x) : 𝓀[K]ˣ) : 𝓀[K]) = IsLocalRing.residue 𝒪[K] (x : 𝒪[K])`:
  the residue-field element underlying the reduction of `x` is the residue of
  the integer underlying `x`.
- **M137.017.** Binders `(K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ)`.
  The value is
  `x ∈ (integerUnitsToResidueUnits K).ker ↔ IsLocalRing.residue 𝒪[K] (x : 𝒪[K]) = 1`.
- **M137.018.** Binders `(K : Type u) [Field K] [ValuativeRel K]`. The value is
  the subgroup equality `principalUnits K 1 = (integerUnitsToResidueUnits K).ker`
  in `Subgroup 𝒪[K]ˣ`.
- **M137.022.** Binders `(K : Type u) [Field K] [ValuativeRel K]`. The value is
  `Function.Surjective (integerUnitsToResidueUnits K)`.

All referenced data (`IntegerUnitsModPrincipalUnits`,
`integerUnitsModPrincipalUnitsMk`, `residueUnitsConcreteEquiv`,
`integerUnitsToResidueUnits`) is the published M137 data of
`ResidueUnits/Definitions.lean`, and `principalUnits` is the published M131.001
definition. No other unit of the source module is referenced.

## Using the targets

The targets are ordinary `def`s, as in the sibling NYLL statement modules. A
proof states its type as the applied target and unfolds it with `change`,
`unfold` or `show`. A theorem `t` of such a type is used as the underlying
proposition by `show _ ↔ _ from t ...` (or `show _ = _ from t ...`); a plain type
ascription `(t ... : _ ↔ _)` keeps the target type and is not accepted by `rw`
or `simp`.

## Modifications

- Namespace prefix `Langlands.NYLL`, and suffix `Statement` on each name.
- Each `theorem` command becomes `def ... : Prop :=` with the former conclusion
  as body; the source proofs are omitted. The `protected` modifier of M137.012
  is kept.
- `set_option linter.unusedVariables false in` is added before M137.012 only.
- The source docstrings are kept unchanged. The source module documentation is
  replaced by documentation of these targets, and a five-line adaptation
  comment follows the copyright header.
- The only import is the M137 data module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits.Definitions`,
  which supplies every constant used. The source namespace,
  `noncomputable section`, `universe u` and `open scoped ValuativeRel`
  (lines 18–24) are retained. There are no instances.

## Reuse boundary

Mathlib's `QuotientGroup.induction_on`, `MonoidHom.mem_ker`,
`ValuationSubring.ker_unitGroupToResidueFieldUnits`,
`ValuationSubring.surjective_unitGroupToResidueFieldUnits` and
`IsLocalRing.surjective_units_map_of_local_ringHom` are the natural proof tools,
but they are stated for Mathlib's own quotient, kernel or
`ValuationSubring.unitGroup` carriers. They do not replace these named targets
about the source's types `IntegerUnitsModPrincipalUnits K`,
`ResidueUnits K` and `principalUnits K 1`.

## Source and licenses

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueUnits.lean`,
SHA-256 `a6c14b9595ff1be38b18be3c1a68841fcd8a85a8a70c2519069027bbefd0e89a`.
Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source path is not listed in the ValuedFieldTheory third-party attribution
table. The published port plan (`notes/reuse/nyll-public-port-plan.md`) records
no NYLL erratum, and the M137 inventory entry
(`notes/reuse/nyll-public-port/m121-m144.md`) lists no patch10 edit for this file.

The original copyright, Apache-2.0 license line and author header are retained.
The Library files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 126 performed this extraction and namespace adaptation. No patch10 edit
or other worker's implementation draft was used.

## Focused development check

The project Lean service built this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) against the published M137 data
module. Checks `c29381df-7a62-46ef-a286-538317ba211f` (M137.012),
`4a1b191e-1a6a-4e90-a445-0b593ebfdd76` (M137.016),
`f7b7f620-d92f-4025-8bdc-1659f18c5e07` (M137.017),
`2ef05346-fae3-46e2-bafc-9a462e838a31` (M137.018) and
`47f033d1-19ab-4a70-b1c1-849ef5c44e25` (M137.022) each returned `ok: true`
with zero errors and warnings, inspected the named target as a definition with
universe parameter `u` whose type returns `Prop`, and found only the axioms
`propext`, `Classical.choice` and `Quot.sound`. A private probe, not
submitted, also proved all five targets from the source proofs. This
establishes compilation, not independent semantic acceptance.
