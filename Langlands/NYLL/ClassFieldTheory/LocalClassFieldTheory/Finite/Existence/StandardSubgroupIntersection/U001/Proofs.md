# Intersecting standard norm conditions: proof

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le`.
Its type is the already published proposition
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_leStatement`
at the universe level `u`:

```lean
theorem unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le :
    unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_leStatement.{u}
```

This is the proof phase of unit M403.001 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m385-m408.md#m403).
The statement module and its Markdown are unchanged.

## Target

By its definition in the published
`StandardSubgroupIntersection.U001.Statements` module, the target is the
closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (ϖ : Kˣ) (d n : Nat)
  (_hϖ : valuationMap K (Additive.ofMul ϖ) = 1),
  unramifiedNormSubgroup K d ⊓
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n ≤
    LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n
```

For a nonarchimedean local field `K` in any universe `u`, a unit `ϖ` of
normalized valuation `1` and arbitrary natural numbers `d` and `n` (zero
included), every unit whose normalized valuation is divisible by `d` and
which lies in `⟨ϖ⟩ · Uⁿ` lies in `⟨ϖ^d⟩ · Uⁿ`. The proof assumes nothing
else: no hypothesis is added, and `d` and `n` are not restricted.

The published objects used are:

- `valuationMap K : Additive Kˣ →+ Int`, the normalized valuation
  (M134.002), defined as `MonoidHom.toAdditive (valuationUnitsMulHom K)`, where
  `valuationUnitsMulHom K` composes `Units.map` of the field valuation, `Units.map`
  of Mathlib's isomorphism `valueGroupWithZeroIsoInt K` onto
  `WithZero (Multiplicative Int)`, and `WithZero.unitsWithZeroEquiv`.
- `unramifiedNormSubgroup K d` (M266.011), whose carrier is
  `{x | (d : Int) ∣ valuationMap K (Additive.ofMul x)}`.
- `uniformizerPrincipalSubgroup K ϖ e n = Subgroup.zpowers (ϖ ^ e) ⊔ fieldPrincipalUnits K n`
  (M289.002), where `fieldPrincipalUnits K n` is the image of `principalUnits K n`
  under `Units.map (algebraMap 𝒪[K] K).toMonoidHom`.
- `integerUnitsToFieldUnits K = Units.map (algebraMap 𝒪[K] K).toMonoidHom`
  (M128.016) and the proved theorem
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits`
  (M128.019): for every `x : 𝒪[K]ˣ`,
  `v K (Additive.ofMul (integerUnitsToFieldUnits K x)) = 0`, where `v K` is
  the normalized integer valuation of M128.001.

## Imports

The module imports exactly two published modules:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection.U001.Statements`,
  the target statement, which brings in `valuationMap`,
  `unramifiedNormSubgroup` and `uniformizerPrincipalSubgroup`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U019.Proofs`,
  the proof of `v_integerUnitsToFieldUnits`, which brings in `v` and
  `integerUnitsToFieldUnits`.

The source's norm-topology, finite abelian subextension, intrinsic absolute
data and separable-units-norm imports are not needed; the focused check below
confirms this.

## Implemented proof

The proof introduces the binders `K`, its four instances, `ϖ`, `d`, `n`, the
hypothesis `hϖ`, a unit `x` and the membership `hx` in the meet, and then
argues as follows.

1. `hx.2` places `x` in `Subgroup.zpowers (ϖ ^ 1) ⊔ fieldPrincipalUnits K n`.
   `Subgroup.mem_sup` (the two subgroups of the commutative group `Kˣ`) gives
   `y ∈ Subgroup.zpowers (ϖ ^ 1)`, `z ∈ fieldPrincipalUnits K n` and `y * z = x`.
   `Subgroup.mem_zpowers_iff` gives `k : Int` with `(ϖ ^ 1) ^ k = y`, simplified
   by `simpa` to `ϖ ^ k = y`.
2. The membership of `z` is restated by `change` as membership in
   `(principalUnits K n).map (integerUnitsToFieldUnits K)`; this is definitional,
   since `integerUnitsToFieldUnits K` and the map in `fieldPrincipalUnits` are the
   same `Units.map (algebraMap 𝒪[K] K).toMonoidHom`. It yields `w ∈ principalUnits K n`
   with `integerUnitsToFieldUnits K w = z`.
3. `valuationMap K (Additive.ofMul z) = 0`: after rewriting `z` as
   `integerUnitsToFieldUnits K w`, the goal is closed by
   `v_integerUnitsToFieldUnits K w`. The comparison of `valuationMap` with `v`
   is definitional and is checked by Lean's `exact`: `valuationMap K a` unfolds to
   `Multiplicative.toAdd (WithZero.unitsWithZeroEquiv u)` for the unit `u` of
   `WithZero (Multiplicative Int)` whose value is
   `valueGroupWithZeroIsoInt K (ValuativeRel.valuation K ↑(Additive.toMul a))`
   (by the definition of `Units.map`), and `WithZero.unitsWithZeroEquiv u` is by
   definition `WithZero.unzero` of this value, which is the defining expression
   of `v K a` up to the proof argument of `unzero`.
4. `valuationMap K (Additive.ofMul x) = k`, by a calculation:
   `Additive.ofMul x = Additive.ofMul y + Additive.ofMul z` (from `y * z = x`,
   definitionally), so `map_add` splits the value; `y = ϖ ^ k` and
   `ofMul_zpow` give `Additive.ofMul y = k • Additive.ofMul ϖ`; `map_zsmul`,
   the hypothesis `hϖ`, `smul_eq_mul` and step 3 give `k * 1 + 0`, which is `k`.
5. `hx.1` is, by the definition of the carrier of
   `unramifiedNormSubgroup K d`, the divisibility
   `(d : Int) ∣ valuationMap K (Additive.ofMul x)`; with step 4 it gives
   `(d : Int) ∣ k`, say `k = d * t`.
6. `y ∈ Subgroup.zpowers (ϖ ^ d)`: by `Subgroup.mem_zpowers_iff` it suffices that
   `(ϖ ^ d) ^ t = ϖ ^ k`, which follows from `zpow_natCast`, `zpow_mul` and
   `k = d * t`.
7. `Subgroup.mem_sup` with `y`, the witness `⟨w, hw, hwz⟩` of step 2 for
   `z ∈ fieldPrincipalUnits K n` (accepted definitionally), and `y * z = x` gives
   `x ∈ uniformizerPrincipalSubgroup K ϖ d n`.

When `d = 0`, step 5 forces `k = 0` and step 6 uses `t` with `0 = 0 * t`; when
`n = 0`, `principalUnits K 0` is all of `𝒪[K]ˣ`. Neither case needs separate
treatment.

## Source and changes

The original is Naganori Yamaguchi's NYLL `ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean#L37-L83),
theorem `LocalClassFieldTheory.unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le`,
signature lines 37–44 and proof lines 45–83 (SHA-256 of the file
`6a1c34851b46b17075888f452875eb49d31dcb167147dfde1eb2e3acc8cb99b1`). It was
read from the retained snapshot under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, with attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement`.

The implemented proof follows the source proof step for step. Worker 472
made these modifications:

| Source | Adapted |
| --- | --- |
| `theorem … (K : Type u) … (hϖ : …) : … := by intro x hx` | the theorem's type is the published `…Statement.{u}`; the proof begins `intro K _ _ _ _ ϖ d n hϖ x hx` |
| namespace `LocalClassFieldTheory` | `Langlands.NYLL.LocalClassFieldTheory` |
| `change z ∈ (principalUnits K n).map (integerUnitsToFieldUnits K) at hz` | unchanged |
| bound unit name `u` | `w`, to avoid shadowing the universe name `u` |
| `exact v_integerUnitsToFieldUnits K u` | `exact v_integerUnitsToFieldUnits K w`, using the published proof (M128.019) |
| `valuationMap_ofMul_mul K y z` | `map_add` after rewriting `Additive.ofMul (y * z)` as `Additive.ofMul y + Additive.ofMul z` by `rfl` |
| `rw [valuationMap_ofMul_zpow, hϖ]` with `ring` | `ofMul_zpow`, `map_zsmul`, `hϖ`, `smul_eq_mul`, then `mul_one` and `add_zero` |
| `(mem_unramifiedNormSubgroup_iff K d x).1 hx.1` | `hx.1`, by the definition of the carrier |
| `ℤ` | `Int` |
| the six source imports | the two published imports listed above |

The source support theorems `valuationMap_ofMul_mul`,
`valuationMap_ofMul_zpow` and `mem_unramifiedNormSubgroup_iff` are not
imported; their uses are replaced as shown by the additive-homomorphism laws
of `valuationMap` and the membership definition. The source file's later
theorems M403.002 and M403.003 are not part of this module.

The original copyright and author header is retained. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) in the Library are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No other worker's draft was reused, and no local, scoped or global instance
or attribute is introduced.

## Development checks

In the approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), focused
check `3ef46dc1-c3e5-43f6-b679-a9f4464807d2` of this module compiled with no errors or warnings and
inspected the theorem with level parameter `u` and axioms `propext`,
`Classical.choice` and `Quot.sound` only. Independent review, the Lake build
and the exact-target check are separate obligations.
