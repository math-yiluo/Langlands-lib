# Residue units and integer units modulo first principal units (M137 data)

For any `K : Type u` with `[Field K]` and a supplied `[ValuativeRel K]`, this
module introduces two new carrier types and the data attached to them:

- `ResidueUnits K`, definitionally the unit group `𝓀[K]ˣ` of the residue field
  of the valuation ring `𝒪[K]`;
- `IntegerUnitsModPrincipalUnits K`, definitionally the actual quotient group
  `𝒪[K]ˣ ⧸ principalUnits K 1` of valuation-ring units by the first principal
  units (the published `Langlands.NYLL.LocalFieldTheory.principalUnits`, whose
  level-one carrier is `{a | (a : 𝒪[K]) - 1 ∈ 𝓂[K] ^ 1}`);

together with their commutative group instances, reflexive comparisons with the
concrete models, finiteness of `ResidueUnits K` when the residue field is
finite, the canonical class map, and the reduction homomorphism
`𝒪[K]ˣ →* ResidueUnits K`. The residue field, valuation ring, units, quotient
and residue map are the canonical Mathlib constructions.

No topology, local-field, discrete-valuation, nontrivial-valuation,
completeness or finite-dimensionality hypothesis is added. The only extra
premise anywhere is the source's `[Finite 𝓀[K]]` on the finiteness instance.

## Source-to-Library map

Every adapted name has prefix `Langlands.NYLL.LocalFieldTheory.`; each
original has prefix `LocalFieldTheory.`. The suffixes are unchanged.

| Unit | Source lines | Kind | Suffix | Meaning |
| --- | --- | --- | --- | --- |
| M137.001 | 26–28 | def | `ResidueUnits` | `𝓀[K]ˣ`, a type in universe `u` |
| M137.002 | 30–35 | instance | `residueUnitsCommGroup` | `CommGroup (ResidueUnits K)` by `change` and `infer_instance` |
| M137.003 | 37–42 | def | `residueUnitsConcreteEquiv` | `ResidueUnits K ≃* 𝓀[K]ˣ`, `MulEquiv.refl` after `change` |
| M137.005 | 52–56 | instance | `residueUnitsFinite` | `Finite (ResidueUnits K)` from `[Finite 𝓀[K]]`, via `Finite.of_equiv` and the symmetric equivalence of M137.003 |
| M137.006 | 58–62 | def | `IntegerUnitsModPrincipalUnits` | `𝒪[K]ˣ ⧸ principalUnits K 1`, a type in universe `u` |
| M137.007 | 64–70 | instance | `integerUnitsModPrincipalUnitsCommGroup` | Canonical quotient `CommGroup` by `change` and `infer_instance` |
| M137.008 | 72–79 | def | `integerUnitsModPrincipalUnitsConcreteEquiv` | `IntegerUnitsModPrincipalUnits K ≃* (𝒪[K]ˣ ⧸ principalUnits K 1)`, `MulEquiv.refl` after `change` |
| M137.009 | 81–87 | def | `integerUnitsModPrincipalUnitsMk` | `𝒪[K]ˣ →* IntegerUnitsModPrincipalUnits K`, the quotient map `QuotientGroup.mk' (principalUnits K 1)` |
| M137.015 | 135–138 | def | `integerUnitsToResidueUnits` | `𝒪[K]ˣ →* ResidueUnits K`, `Units.map (IsLocalRing.residue 𝒪[K]).toMonoidHom` |

Source lines include each docstring and attribute line. The telescope of every
declaration is exactly the source's: `(K : Type u) [Field K] [ValuativeRel K]`
for all nine, followed for M137.005 only by `[Finite 𝓀[K]]`. All binders are
explicit or instance binders as in the source; no implicit argument is added.

The source attributes are retained: `@[implicit_reducible]` on M137.006,
M137.007 and M137.009, and the `noncomputable` modifier on M137.005 (inside the
retained `noncomputable section`). M137.006 is a `def`, not an `abbrev`, so the
named instance M137.007 supplies its group structure and `change`/`show`
unfolds it, exactly as in the source.

## Bodies and instances

All nine declaration bodies are copied unchanged, including every `change`,
`infer_instance`, `exact`, `MulEquiv.refl`, `Finite.of_equiv`,
`QuotientGroup.mk'` and `Units.map` term, and all type ascriptions. No
separate quotient or unit model and no assumed equivalence is introduced: both
comparisons are literally `MulEquiv.refl _` on the unfolded carrier.

The three instances have the two new types `ResidueUnits K` and
`IntegerUnitsModPrincipalUnits K` as heads. The two group instances are
obtained by `infer_instance` after `change`, so each is definitionally the
canonical Mathlib structure on the unfolded carrier (the unit-group
`CommGroup` of `𝓀[K]ˣ`, respectively the quotient `CommGroup` of
`𝒪[K]ˣ ⧸ principalUnits K 1`); the finiteness instance is a `Prop`. Hence no
instance with data differing from Mathlib or the Library is added.

## Units not ported

The source units M137.004 (`residueUnitsConcreteEquiv_apply`), M137.010–.011,
M137.013–.014 (including the lift `integerUnitsModPrincipalUnitsLift`),
M137.019–.021 and M137.023–.034 (every declaration from source line 215 on)
are not listed by the task, and none of the nine listed data
units or five listed statement targets refers to them. They are
excluded, as are all source theorem commands. The listed theorems M137.012,
M137.016, M137.017, M137.018 and M137.022 are published separately as
Prop-valued targets in `ResidueUnits/Statements.lean`.

## Modifications

- The source namespace `LocalFieldTheory` becomes
  `Langlands.NYLL.LocalFieldTheory`; the declaration names are otherwise
  unchanged.
- The source imports `Mathlib.SetTheory.Cardinal.Finite`,
  `Mathlib.Algebra.Category.ModuleCat.Basic`,
  `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.AdditiveEquiv`
  and `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits`
  (source lines 7–10) are replaced by
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions`
  (the published `principalUnits`), `Mathlib.GroupTheory.QuotientGroup.Basic`
  (quotient groups and `QuotientGroup.mk'`) and
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs` (residue field and
  `IsLocalRing.residue`). The removed imports serve only the excluded
  cardinality, additive-equivalence and module-category units.
- The source module documentation (lines 11–16), which also describes the
  excluded additive comparison, is replaced by documentation of these units.
  The individual declaration docstrings are unchanged.
- The source namespace, `noncomputable section`, `universe u` and
  `open scoped ValuativeRel` (lines 18–24) are retained, and the module closes
  with `end` and `end Langlands.NYLL.LocalFieldTheory`.
- A three-line adaptation comment is added after the copyright header.

## Reuse boundary

Mathlib's `ValuationSubring.unitGroupToResidueFieldUnits` and
`ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits` work with a
`ValuationSubring A` of a field, its unit group `A.unitGroup` (a subgroup of
field units) and `A.principalUnitGroup`. They do not have the source's carriers
`𝒪[K]ˣ` (units of `Valuation.integer (ValuativeRel.valuation K)`) and
`principalUnits K 1`, so they cannot replace these declarations with the source
types. They and Mathlib's `IsLocalRing.ResidueField` and `Units` are reused only
as the canonical constructions named above. The Library contains no earlier
declaration with these names or carriers.

## Source and licenses

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueUnits.lean`.
The complete source file SHA-256 is
`a6c14b9595ff1be38b18be3c1a68841fcd8a85a8a70c2519069027bbefd0e89a`, which
matches the author's publication manifest. Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source path is not listed in the ValuedFieldTheory third-party attribution
table, so no third-party code is copied. The published port plan
(`notes/reuse/nyll-public-port-plan.md`) records no NYLL erratum, and the M137
inventory entry (`notes/reuse/nyll-public-port/m121-m144.md`) lists no patch10
edit for this file.

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
`5ed2965256430c3649e86755f9576b54eca72435`). Check
`a4d814e1-63c2-45d3-9b09-3acf16aa2e1f` returned `ok: true` with zero errors
and warnings; it inspected `integerUnitsToResidueUnits` as a definition with
universe parameter `u` and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. This establishes compilation, not independent semantic acceptance.
