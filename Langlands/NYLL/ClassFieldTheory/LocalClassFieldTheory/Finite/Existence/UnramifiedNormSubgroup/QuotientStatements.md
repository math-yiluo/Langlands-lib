# Unramified norm classes: proposition targets

The four targets concern the published canonical quotient homomorphism
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormClass K n :
Kˣ →* Kˣ ⧸ unramifiedNormSubgroup K n`. Its kernel target has exactly the
source orientation: the kernel of this homomorphism equals the published
subgroup. The subgroup is defined by integer divisibility of the published
normalized unit valuation
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`.
The targets here assert no identification with an extension's norm group.

Each target is a closed `def ... : Prop := ∀ ...`. The source telescope
is retained: `K : Type u` at arbitrary universe `u`, instances
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
then `n : Nat`, and `x : Kˣ` where present. The degree is unrestricted,
including `n = 0`. These are proposition definitions; no proof is asserted.

| Source unit | Target (after `Langlands.NYLL.LocalClassFieldTheory.`) | Meaning |
| --- | --- | --- |
| M266.014 | `unramifiedNormClass_surjectiveStatement` | Every unramified norm class is represented by a field unit. |
| M266.015 | `unramifiedNormClass_kerStatement` | The kernel of the canonical quotient map is the published unramified norm subgroup. |
| M266.016 | `unramifiedNormClass_eq_one_iffStatement` | A unit has trivial class exactly when n divides its normalized valuation. |
| M266.017 | `unramifiedNormClass_eq_one_iff_memStatement` | A unit has trivial class exactly when it belongs to the published subgroup. |

## Source and changes

The original module is `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean` in Naganori Yamaguchi's ClassFieldTheory,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`. The full source was read; its SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It is registered in `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path above.
No applicable errata entry was found in the project notes.

| Source declaration (after `LocalClassFieldTheory.`) | Source lines | Adapted declaration (after `Langlands.NYLL.LocalClassFieldTheory.`) |
| --- | --- | --- |
| `unramifiedNormClass_surjective` | 156–159 | `unramifiedNormClass_surjectiveStatement` |
| `unramifiedNormClass_ker` | 162–166 | `unramifiedNormClass_kerStatement` |
| `unramifiedNormClass_eq_one_iff` | 169–176 | `unramifiedNormClass_eq_one_iffStatement` |
| `unramifiedNormClass_eq_one_iff_mem` | 179–183 | `unramifiedNormClass_eq_one_iff_memStatement` |

Worker 205 extracted these related theorem statements, added the namespace
prefix and modification record, universally quantified the original telescopes
in Prop-valued definitions, and appended `Statement` to each name. The
expressions, universe, parameter order and hypotheses are unchanged.
Source proofs are reserved for separate proof contributions.

The sole import is the published
`UnramifiedNormSubgroup.U013.Definitions`, which imports the published
`U011.Definitions` subgroup and Mathlib's quotient-group definitions.
No preceding M266 theorem or unrelated source import is needed to state
these targets. No new instance is introduced.

The original copyright and author header is retained. Apache-2.0 license and
notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
No earlier adaptation or another worker's draft was reused.

A focused Lean-service check in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the module with zero errors
and warnings. Inspection of `unramifiedNormClass_surjectiveStatement`
reported `statement_returns_prop: true` with universe parameter `u`.
This check establishes that the published quotient-projection import suffices
to state all four targets.
