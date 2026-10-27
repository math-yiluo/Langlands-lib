# Principal-unit membership and the zeroth subgroup: proofs

This module proves the two published closed targets in
`Langlands.NYLL.LocalFieldTheory`:

| Theorem | Complete type | Source unit |
| --- | --- | --- |
| `mem_principalUnits_iff.{u}` | `MemPrincipalUnitsIffStatement.{u}` | M131.002 |
| `principalUnits_zero.{u}` | `PrincipalUnitsZeroStatement.{u}` | M131.004 |

Each theorem has no parameters or premises of its own. Its unapplied type is
exactly the named statement, with that statement's single arbitrary universe
`u` retained. For `K : Type u` with `Field K` and the supplied
`ValuativeRel K`, write `𝒪[K] = Valuation.integer (ValuativeRel.valuation K)`
for the actual valuation integer ring and `𝓂[K]` for its canonical maximal
ideal `IsLocalRing.maximalIdeal 𝒪[K]`. The targets assert:

- for every unit `a : 𝒪[K]ˣ` and every natural number `n`, including zero,
  `a ∈ principalUnits K n ↔ ((a : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])`;
- `principalUnits K 0 = (⊤ : Subgroup 𝒪[K]ˣ)`, equality in the subgroup
  lattice of valuation-ring units.

Here `principalUnits` is the published
`Langlands.NYLL.LocalFieldTheory.principalUnits`. No topology, discreteness,
local-field, residue-finiteness, completeness, characteristic or
nontrivial-valuation hypothesis occurs, and neither conclusion is assumed.

## Implemented proofs

**Membership.** After introducing the field, its two instances, the unit `a`
and the index `n`, the proof is `Iff.rfl`. The published definition builds
`principalUnits K n` with carrier
`{u | ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])}`, so membership of `a` in
the subgroup unfolds definitionally to membership of `a - 1` in the ideal
power. Nothing depends on the value of `n`; the case `n = 0` is covered by
the same term.

**Zero step.** After introducing the field and its two instances, `ext a`
reduces subgroup equality to the membership statement
`a ∈ principalUnits K 0 ↔ a ∈ ⊤` for an arbitrary unit `a`. Then
`simp [principalUnits]` closes the goal. Unfolding the definition exposes
the carrier condition `(a : 𝒪[K]) - 1 ∈ 𝓂[K] ^ 0`. The lemmas reported by
`simp?` in a private development check were `pow_zero` and
`Ideal.one_eq_top`, which turn `𝓂[K] ^ 0` into the top ideal;
`Submodule.mem_top`, which makes the condition true; the structure
membership lemmas `Subgroup.mem_mk`, `Submonoid.mem_mk`,
`Subsemigroup.mem_mk`, with `Set.ofPred_true` and `Set.mem_univ`; and
`Subgroup.mem_top` on the right-hand side. Both sides therefore hold for
every unit.

No auxiliary definition, statement or lemma is introduced. Every result used
is either the imported published definition or a Mathlib lemma named above.

## Source correspondence and modifications

The source is Naganori Yamaguchi's NYLL `ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean#L19-L76),
SHA-256 `1b36c019d270961f321ca891ae155fb4fd658d4e29ed97ba78e30fbee00a5047`.
Lines 19–76 were read in full from the registered snapshot.

| Source declaration | Source lines | Adapted theorem |
| --- | --- | --- |
| `LocalFieldTheory.mem_principalUnits_iff` | 54–57 | `Langlands.NYLL.LocalFieldTheory.mem_principalUnits_iff` |
| `LocalFieldTheory.principalUnits_zero` | 73–76 | `Langlands.NYLL.LocalFieldTheory.principalUnits_zero` |

The source proofs are retained: `Iff.rfl` for membership, and `ext u`
followed by `simp [principalUnits]` for the zero step (the extensionality
variable is renamed `a`). The source docstrings (lines 52–53 and 72) are kept
verbatim. The changes are:

- the namespace is prefixed with `Langlands.NYLL`;
- the source theorems take `K`, the instances, the unit and the index as
  theorem arguments; here each theorem's type is the published closed
  proposition, so the proofs first introduce these binders (`fun _ _ _ _ _`
  for membership, `intro K _ _` for the zero step);
- the zero theorem's `@[simp]` attribute is not retained, because its type
  is now a closed proposition rather than a rewrite rule.

The intervening source theorem M131.003, `principalUnits_integerRingEquiv_mem`
(lines 59–70), is not used and not ported. Neither proof needs it, and the
conservative M131.003 scheduling edge in the NYLL declaration partition is not
a mathematical dependency here. No antitonicity, quotient, automorphism,
inertia or reciprocity result is introduced.

## Imports

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Statements`,
which supplies both targets and, through its own import of the published
`...PrincipalUnits.Definitions`, the definition `principalUnits` together with
Mathlib's `Mathlib.Topology.Algebra.Valued.ValuativeRel`,
`Mathlib.RingTheory.Ideal.Operations` and `Mathlib.Tactic.Ring`. Those Mathlib
modules provide every lemma used by `simp`. The source's broad import of
NYLL's `NonarchimedeanLocalField.Basic` is not ported.

## Attribution

The registered original is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; its
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. No errata
directory exists under the project `notes/` or the published Library `notes/`,
so no applicable errata file was found. The selected file is listed neither in
the source's root `NOTICE` nor in the supplement's `ANTHROPIC_FLT_SOURCE.md`
inventories, so no third-party source is copied.

The Lean file keeps the original copyright and author header and records
Worker 229's adaptation. The unchanged upstream Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already in the Library,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 229 wrote this module. No other worker's implementation draft is
reused; Worker 106 supplied task routing only.

## Development check

The project Lean service built this module in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with zero errors and warnings.
Declaration inspections `3f9c7bd3-b44b-43c8-bf62-279163daa06c` and
`b38a573f-ad11-44d9-86de-4ebb54ab003b` each reported a theorem with level
parameters `[u]` and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. A private diagnostic `00c2be91-09cf-4e9f-b732-cf8fb81d55f7`
printed `mem_principalUnits_iff.{u_1} : MemPrincipalUnitsIffStatement.{u_1}`
and `principalUnits_zero.{u_1} : PrincipalUnitsZeroStatement.{u_1}`, with the
statements' full bodies. These are development checks; exact-target validation
and independent acceptance are separate.
