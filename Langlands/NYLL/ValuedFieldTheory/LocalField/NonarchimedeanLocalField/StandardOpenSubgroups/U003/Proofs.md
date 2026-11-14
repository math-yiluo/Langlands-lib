# Principal units inside every neighborhood of one

This pair proves the existing Library target
`Langlands.NYLL.LocalFieldTheory.exists_fieldPrincipalUnits_subset_of_mem_nhdsStatement`.
Its theorem is
`Langlands.NYLL.LocalFieldTheory.exists_fieldPrincipalUnits_subset_of_mem_nhds`
in module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.U003.Proofs`.

The complete theorem telescope is

```lean
(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]
(U : Set Kˣ) (hU : U ∈ Filter.nhds (1 : Kˣ)) :
  exists_fieldPrincipalUnits_subset_of_mem_nhdsStatement K U hU
```

Here `u` is arbitrary. Unfolding the target, the conclusion is
`∃ n : Nat, 1 ≤ n ∧ (fieldPrincipalUnits K n : Set Kˣ) ⊆ U`.
The local-field class, valuation ring, maximal ideal, unit-group topology,
and `fieldPrincipalUnits` are the unchanged published objects. In particular,
`fieldPrincipalUnits K n` is the image of units congruent to one modulo
`𝓂[K]^n` under `Units.map (algebraMap 𝒪[K] K).toMonoidHom`.
No hypothesis is added and no target or imported declaration is edited.

## Implemented proof

Choose an open set `H` containing one and contained in `U` using
`mem_nhds_iff`. The embedding `Units.isEmbedding_val₀` represents `H` as
the inverse image of an open set `V` in the field, and `1 ∈ V` follows.
The inverse image `s` of `V` under the continuous map
`𝒪[K] → K`, `a ↦ (a : K) + 1`, is a neighborhood of zero.

The local fact `hPower` proves that some `𝓂[K]^N` is contained in `s`.
It uses `mem_nhds_subtype` to find a field neighborhood of zero, then
`IsValuativeTopology.hasBasis_nhds_zero` to find a valuation ball inside it.
Mathlib supplies an irreducible element of the discrete valuation ring
`𝒪[K]`. Its valuation is less than one by
`Valuation.integer.v_irreducible_lt_one`, and `exists_pow_lt₀` gives a
power with valuation below the ball's radius. The equality
`Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow` then puts the
corresponding maximal-ideal power inside the ball. These properties follow
from the existing local-field instances; they are not additional premises.
`hPower` is a local proof inside the theorem, not a new exported statement
or an invocation of an unproved NYLL theorem.

Take `n = N + 1`; `Nat.succ_pos N` proves the required `1 ≤ n`.
An element of `fieldPrincipalUnits K (N + 1)` has a valuation-ring unit
preimage `a`. The published theorem `mem_principalUnits_iff` puts `a - 1`
in `𝓂[K]^(N + 1)`. The inclusion `Ideal.pow_le_pow_right (Nat.le_succ N)`
puts it in `𝓂[K]^N`, hence in `s`. After applying the valuation-ring
inclusion and cancelling `-1 + 1`, the image of `a` lies in `V`, its
field-unit image lies in `H`, and therefore it lies in `U`.

The only imports are the unchanged target module
`StandardOpenSubgroups.Statements` and the published membership proof
module `PrincipalUnits.Proofs`, under the common prefix
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField`.
Their Mathlib closure supplies the topology and valuation lemmas above.
The proof uses no unpublished result or extra supplied structure.

## Source correspondence and modifications

The pinned original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
Both source files are under
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/`.

| Source file and unit | Exact passage reused | File SHA-256 |
| --- | --- | --- |
| `StandardOpenSubgroups.lean`, M289.003 | docstring 43, signature 44–48, proof 48–84 | `9cf6baf50519f650504762782a5aed12500479b911fc1ac4db9a138207097d7d` |
| `PrincipalUnitQuotients.lean`, M132.012 | signature 162–166, proof 167–185 | `6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83` |

The passages were read directly from the retained registered snapshot at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registration is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No matching errata file for either source ID was present under the supplied
Library's `notes/errata/`.

Worker 559 made these modifications on 14 November 2026:

- Prefix the namespace with `Langlands.NYLL` and prove the fully applied
  existing `Statement` target, retaining all source parameters, their order,
  the arbitrary universe, and the positive-index conclusion.
- Replace the broad source import with the two focused published imports;
  explicitly open `Filter` and omit unused source namespace openings.
- Replace the source call to `exists_maximalIdeal_pow_subset_nhds_zero`
  with its M132.012 Mathlib proof, locally inlined as `hPower`. The independent
  public proof of M132.012 is a separate task and is not assumed here.
- Expand `integerUnitsToFieldUnits K` to its published defining expression
  `Units.map (algebraMap 𝒪[K] K).toMonoidHom`, matching the imported
  `fieldPrincipalUnits` definition. Rename the preimage unit and associated
  local hypotheses from `u` to `a`; adjust whitespace and spell `ℕ` as `Nat`.
- Retain the source noncomputable section and theorem docstring, and replace
  the broad file documentation with a focused proof title and this explanation.

No other source theorem is added. The proof supplies M289.003 only.

## Attribution and validation

The original copyright, author header and Apache-2.0 notice are preserved
verbatim in Lean. The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are reused unchanged. Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively. The Lean modification notice identifies both reused passages.

Development compilation in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` succeeded with zero errors and zero
warnings, diagnostic `116b728b-1d08-4224-b50c-dbf0b75e2bc2`.
A further Lake build and declaration inspection succeeded, diagnostic
`4f3e83f8-2adc-4e64-9b6d-41f5f123e809`, again with zero errors and warnings.
Inspection identifies a theorem with level parameters `[u]` and only the standard
assumptions `propext`, `Classical.choice` and `Quot.sound`.
This environment uses Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from independent semantic review,
exact-target validation and integration.
