# NYLL M120: principal-unit quotient and subquotient data

This module preserves the image of a filtration subgroup in an ambient
quotient, the actual subgroup quotient at any two levels, its canonical
group structures, the explicit identity equivalence to its concrete
representation, and the canonical quotient homomorphism.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean` (M120).
The original file SHA-256 is
`30ce59edb8590e15afdaaef8d9551282e240c576f09be0ad55d12b09e9e4d807`.
The readable original is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean`
under registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration | Source declaration lines | Adapted declaration |
| --- | --- | --- | --- |
| M120.024 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubgroupClassInQuotient` | 233–237 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubgroupClassInQuotient` |
| M120.025 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubgroupClassInQuotient_normal` | 240–245 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubgroupClassInQuotient_normal` |
| M120.028 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotient` | 273–275 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotient` |
| M120.029 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientGroup` | 281–288 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientGroup` |
| M120.030 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientConcreteEquiv` | 291–304 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientConcreteEquiv` |
| M120.031 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientCommGroup` | 308–316 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientCommGroup` |
| M120.032 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientMk` | 319–328 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientMk` |

All original docstrings immediately preceding the declarations are retained.
The original shared context is `universe u v` and
`variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)` within
`LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration`.

## Complete telescopes and constructions

For M120.024–025, M120.028–030 and M120.032, the complete outer telescope
starts with `{G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)` and
then `(m n : ℕ)`. M120.024, M120.029–030 and M120.032 next take
`[(U.principalUnitSubgroup n).Normal]`; M120.025 takes that instance followed
by `[(U.principalUnitSubgroup m).Normal]`. M120.028 has no normality instance.
No declaration in this module has an `m ≤ n` hypothesis.

M120.031 instead has exactly `{H : Type u} [CommGroup H]
(V : AntitoneSubgroupFiltration H) (m n : ℕ)
[(V.principalUnitSubgroup n).Normal]`; no unused `G`, `Group G` or `U`
parameter is generalized into this declaration. The carrier universe `u`
and the unused universe declaration `v` are retained from the source.

The actual constructions are:

- `principalUnitSubgroupClassInQuotient`: the subgroup image
  `Subgroup.map (QuotientGroup.mk' (U.principalUnitSubgroup n))
  (U.principalUnitSubgroup m)` in `G ⧸ U.principalUnitSubgroup n`.
- `principalUnitSubgroupClassInQuotient_normal`: the original proof unfolds
  this image and calls `infer_instance`, using normality of both levels.
- `principalUnitSubquotient`: the type
  `U.principalUnitSubgroup m ⧸
  (U.principalUnitSubgroup n).subgroupOf (U.principalUnitSubgroup m)` in
  `Type u`. For arbitrary indices the denominator is the subgroup induced
  inside level `m`; antitonicity gives the usual `U^m/U^n` when `m ≤ n`.
- `principalUnitSubquotientGroup`: the original proof changes to the concrete
  quotient and infers its Mathlib group structure.
- `principalUnitSubquotientConcreteEquiv`: the original proof changes both
  sides to the same concrete quotient and returns `MulEquiv.refl _`.
- `principalUnitSubquotientCommGroup`: the original structure extends the
  inferred quotient `Group`, proves commutativity by injectivity of the
  concrete equivalence, rewrites with `map_mul`, and applies `mul_comm`.
- `principalUnitSubquotientMk`: the original proof changes the target to the
  concrete quotient homomorphism type and returns `QuotientGroup.mk'` for
  the induced subgroup.

## Modifications and reuse

Worker 321 added the `Langlands.NYLL` namespace prefix, extracted only the
listed declarations and replaced the three original Mathlib imports by
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Filtration`.
That module retains all three source imports. A new module-level comment
records these changes. Every declaration header, construction body,
embedded proof, instance scope and priority, and original docstring is
otherwise unchanged. No source theorem or unpublished external-module
helper is required.

The Library and Mathlib were searched before porting. The definitions reuse
Mathlib subgroup images, induced subgroups, quotient groups and homomorphisms
directly. The source instances keep their original global scope under new
qualified names and apply to these filtration expressions; no instance is
added to Mathlib's namespaces or to unrelated existing Library types.

## Attribution and scope

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, Apache-2.0, author Naganori Yamaguchi (assisted by
OpenAI Codex). The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The public inventory records no patch10 modification for M120. Worker 321
made the extraction and namespace/import changes described above, without
reusing another worker's draft or compatibility patch.

These are source data and source instances with embedded construction
proofs. No separate source theorem, proposition target or proof artifact is
asserted here. In particular, the explanatory source docstring about a
kernel under `m ≤ n` is not a new kernel theorem publication. This module
asserts no host reciprocity or class-formation result.
