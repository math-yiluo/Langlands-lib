# Openness of the valuation-integer unit subgroup

This module proves the published proposition
`Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup_isOpenStatement`
by the theorem
`Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup_isOpen`. The theorem
has the full interface

```lean
theorem Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup_isOpen
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup_isOpenStatement K
```

Its type is exactly the published target applied to the source parameters.
The arbitrary universe `u`, the explicit field `K` and the four instances
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`
are retained in the source order. `IsNonarchimedeanLocalField` is Mathlib's
root class. No subgroup, openness, uniform-structure or other extra hypothesis
is supplied.

Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology.Statements`.
That published Lean/Markdown pair, the `UnitTopology.U001.Definitions` and
`Basic.U016.Definitions` pairs it imports, and the rest of its import chain
remain unchanged.

## Target and mathematical meaning

Unfolded, the target is

```lean
IsOpen (Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup K : Set Kˣ)
```

The subgroup is the published actual image
`MonoidHom.range (integerUnitsToFieldUnits K)`, where
`integerUnitsToFieldUnits K = Units.map (algebraMap 𝒪[K] K).toMonoidHom` maps
units of Mathlib's valuation-integer subring `𝒪[K]` into `Kˣ`. The topology on
`Kˣ` is Mathlib's native units topology induced by the supplied topology on
`K`. The theorem says that this image is an open subset of `Kˣ`.

## Implemented proof

The proof has three steps, all inside the single theorem.

1. **Membership (local step `hmem`).** For every `x : Kˣ`,
   `x ∈ localBaseUnitSubgroup K ↔ ValuativeRel.valuation K (x : K) = 1`.
   - Forward: write `x` as the image of `a : 𝒪[K]ˣ`. Mathlib's
     `Valuation.integer.integers (ValuativeRel.valuation K)` says that
     `𝒪[K]` is the integer ring of the canonical valuation, and
     `Valuation.Integers.valuation_unit` gives valuation `1` for the image of
     a unit of that ring. `simpa [integerUnitsToFieldUnits]` unfolds the
     published inclusion map to match the goal.
   - Backward: if `valuation K x = 1`, then `x` and `x⁻¹` both have
     valuation at most one (`Valuation.mem_integer_iff`; for the inverse
     `simp [hx]`). This gives an explicit unit `a : 𝒪[K]ˣ` with value
     `⟨x, _⟩` and inverse `⟨x⁻¹, _⟩`; the two unit equations follow from
     `mul_inv_cancel₀` and `inv_mul_cancel₀` using `x.ne_zero`. Its image is
     `x` by extensionality and `rfl`.
2. **Open sphere.** `hsphere : IsOpen {x : K | valuation K x = 1}` comes from
   Mathlib's `Valuation.isOpen_sphere` for the canonical valuation, which
   applies through the `IsValuativeTopology K` parent of
   `IsNonarchimedeanLocalField K`, at radius `1 ≠ 0`. `simpa only` with
   `Valuation.restrict_eq_one_iff` turns the restricted-valuation sphere
   into this set.
3. **Pull back to units.** `hpre` is the preimage of `hsphere` under the
   continuous coercion `Units.continuous_val : Continuous (fun x : Kˣ => (x : K))`.
   After `unfold localBaseUnitSubgroup_isOpenStatement`, the goal's set is
   rewritten by extensionality and `hmem` to
   `{x : Kˣ | valuation K (x : K) = 1}`, and `hpre` closes the goal.

The proof does not use local compactness or non-discreteness. Only the
valuative topology and the canonical valuation are used.

Compilation with environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) gives zero
errors and warnings (private development diagnostic
`477691a7-14cc-40b6-b8bd-c6c4ea05e907` for this workspace module). The theorem keeps universe `u` and
depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. This development check is not acceptance.

## Source correspondence and modifications

The original is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean>),
SHA-256 `77d63306c40bd28166878221e43427bbbcd699daeee497bbe40c82935d928f43`
(recomputed by Worker 127 on 13 November 2026). The full file was read.

| Source unit and original name | Original lines | Here |
| --- | --- | --- |
| M256.003, `LocalFieldTheory.localBaseUnitSubgroup_isOpen` | 61–77; declaration 63–66, proof 67–77 | `localBaseUnitSubgroup_isOpen`, docstring and steps 2–3 |
| M256.002, `LocalFieldTheory.mem_localBaseUnitSubgroup_iff_valuation_eq_one` | 33–59; proof 38–59 | Proof reused as the local `have hmem` (step 1) |
| M256.001, `LocalFieldTheory.localBaseUnitSubgroup` | 28–31 | Published `UnitTopology.U001.Definitions`, reused unchanged |

The source docstring is kept unchanged. The changes are:

- Prefix the namespace `LocalFieldTheory` with `Langlands.NYLL`. The opened
  inclusion-map namespace becomes
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`.
- State the conclusion as the published target
  `localBaseUnitSubgroup_isOpenStatement K` and add
  `unfold localBaseUnitSubgroup_isOpenStatement` before the source `rw`.
- The source's `rw [show ... by ext x; exact mem_localBaseUnitSubgroup_iff_valuation_eq_one K x]`
  cites the separate M256.002 theorem. Its exact proof is still separate
  work (Task 5749, intended module `UnitTopology.U002.Proofs`) and is not in
  the Library at this proof's base `9b849caba7c63ede041b7fec49c90ceaafb08568`.
  So this module adds the local hypothesis
  `hmem : ∀ x : Kˣ, x ∈ localBaseUnitSubgroup K ↔ ValuativeRel.valuation K (x : K) = 1`.
  Its proof is `intro x`, followed by source lines 38–59 unchanged except
  for indentation. The final `rw` cites `hmem x` instead of the source
  theorem. No public
  declaration named `mem_localBaseUnitSubgroup_iff_valuation_eq_one` (or any
  other auxiliary declaration) is added, so there is no clash with Task 5749.
  The task context explicitly allows proving the openness target directly
  from published data and Mathlib.
- Replace the full NYLL Basic import (source line 7) with the published
  `UnitTopology.Statements` import. Retain `noncomputable section`, universe
  `u` and `open scoped ValuativeRel`. Omit the subgroup definition (already
  published) and the separate M256.002 theorem.
- Steps 2 and 3 (`hsphere`, `hpre` and the final `rw`/`exact`) are source
  lines 67–77. Besides the added `unfold` and the `hmem x` citation, the only
  change is layout: `hsphere`'s `:=` and `by` are joined on one line.

The [public partition](../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m256)
lists M256.003 after `M256.002.END`. This proof does not wait for that edge
because it inlines M256.002's argument.

## Attribution and status

The registered original source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; the
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The Lean
file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0 and
author header verbatim ("Naganori Yamaguchi (assisted by OpenAI Codex)"),
followed by Worker 127's dated modification record. The unchanged
Apache-2.0 [LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) remain in
`licenses/NYLL/`. No UnitTopology-specific NOTICE entry or patch10 change
applies. There are no project coauthors.

This proof establishes only M256.003. It does not publish the M256.002
membership theorem as a named result, and it establishes no host
class-formation, cup-product, transfer, Tate or reciprocity result. The
related host `Langlands.PadicField.TopologicalData.unitSubgroup`, which uses
supplied p-adic data, is not involved.
