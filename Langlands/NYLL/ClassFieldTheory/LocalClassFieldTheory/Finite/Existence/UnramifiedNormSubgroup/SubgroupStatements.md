# The unramified norm subgroup: proposition targets

The targets relate the published subgroup
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup K n` of
the actual field-unit group `Kˣ` to the published normalized valuation
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`
and its published multiplicative reduction
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegreeMulHom K n`.
The source equality keeps its orientation:
`MonoidHom.ker (valuationModDegreeMulHom K n) = unramifiedNormSubgroup K n`.
The subgroup carrier was already defined by valuation divisibility;
these targets do not assume that it is an extension norm subgroup.

Every target is a closed `def ... : Prop := ∀ ...`. It retains the source's
`K : Type u` at arbitrary universe `u` and the instance parameters
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
then `n : Nat`, followed by the source unit arguments in their original order.
There is no positivity or nonzero-modulus assumption; the targets also cover
`n = 0`. These are proposition definitions, with no asserted theorem or axiom.

| Source unit | Target (after `Langlands.NYLL.LocalClassFieldTheory.`) | Meaning |
| --- | --- | --- |
| M266.012 | `mem_unramifiedNormSubgroup_iffStatement` | Membership is divisibility of the normalized unit valuation by n. |
| M266.018 | `unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHomStatement` | The kernel of the multiplicative reduced valuation equals the published unramified norm subgroup. |
| M266.019 | `mem_unramifiedNormSubgroup_iff_valuationModDegreeMulHom_eq_oneStatement` | Membership is equivalent to the multiplicative reduced valuation being one. |

## Source and changes

The original module is
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The full original was read; its SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It is registered in `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path above.
No applicable errata entry was found in the project notes.

| Source declaration (after `LocalClassFieldTheory.`) | Source lines | Adapted declaration (after `Langlands.NYLL.LocalClassFieldTheory.`) |
| --- | --- | --- |
| `mem_unramifiedNormSubgroup_iff` | 143–147 | `mem_unramifiedNormSubgroup_iffStatement` |
| `unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom` | 186–191 | `unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHomStatement` |
| `mem_unramifiedNormSubgroup_iff_valuationModDegreeMulHom_eq_one` | 195–199 | `mem_unramifiedNormSubgroup_iff_valuationModDegreeMulHom_eq_oneStatement` |

Worker 205 added the namespace prefix and modification record, extracted these
related targets, changed each theorem to a closed Prop-valued definition by
universally quantifying its original telescope, and appended `Statement` to
its name. The mathematical expressions, universes, parameter order and
hypotheses are unchanged. Source theorem proofs and simp attributes are
reserved for separate proof contributions. The imports are only:

- Published `UnramifiedNormSubgroup.U011.Definitions`.
- Published `UnramifiedNormSubgroup.U006.Definitions`.

This focused set of published data suffices to state the targets; the source's
earlier theorem proofs and other module imports are not used here.
No global or local instance is introduced.

The original copyright and author header is retained. Apache-2.0 license and
notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
No earlier adaptation or another worker's draft was reused.

The focused Lean-service check in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the entire module with zero
errors and warnings. Inspection of
`unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHomStatement` confirmed
`statement_returns_prop: true` and universe parameter `u`. The successful
check verifies that the two published data imports suffice for all three
targets, without the source's quotient projection or preceding theorem proofs.
