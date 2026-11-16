# Conjugating an abstract field does not change its degree image

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.fieldImage_conjugate`, the proof phase of
M027.001 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m027).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.fieldImage_conjugateStatement` applied to the
theorem's parameters:

```lean
theorem DegreeData.fieldImage_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (D : DegreeData G) (K : ClosedSubgroup G) (σ : G) :
    DegreeData.fieldImage_conjugateStatement D K σ
```

## Target and binders

The theorem binds its own `{G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]` and takes `D`, `K` and `σ`, exactly as the published target and the source theorem; the module declares no section variables.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.FieldImageConjugate.Statements`, the target is the proposition

```lean
D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K
```

Here `D : DegreeData G` (M010.002) is a degree datum with continuous degree `D.degree : G →ₜ* ZHatMul`, `D.fieldImage K` (M010.010) is the image `d(G_K)` of the restricted degree, a subgroup of `ZHatMul`, and `conjugateClosedSubgroup K σ` (M026.001) is the closed subgroup with underlying subgroup `ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, that is `σ⁻¹ G_K σ`, the subgroup of the right conjugate field `K^σ`. The target says that `K` and its conjugate `K^σ` have the same degree image. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.FieldImageConjugate.Statements`, which defines the target and imports `fieldImage` (M010.010) and `conjugateClosedSubgroup` (M026.001);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U011.Proofs`, the published proof of M010.011 `DegreeData.fieldImage_eq_map`, of type `fieldImage_eq_mapStatement D K`, which unfolds to `D.fieldImage K = K.toSubgroup.map D.degree.toMonoidHom`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs`, the published proof of M026.002 `conjugateClosedSubgroup_mem`, of type `conjugateClosedSubgroup_memStatement K σ x`, which unfolds to `x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K`.

The module opens no namespace; the source's `open KummerTheory` and `open CyclicCohomology` are not needed.

## Implemented proof

After `show` states the published proposition unfolded, the proof states the unfolded forms of the two `...Statement`-typed published results it rewrites with as local facts: `hKσ` and `hK` are M010.011 `fieldImage_eq_map` for `conjugateClosedSubgroup K σ` and for `K`, and `hmem x` is M026.002 `conjugateClosedSubgroup_mem K σ x`. The rest is the source proof with `rw [hKσ, hK]` in place of `rw [D.fieldImage_eq_map, D.fieldImage_eq_map]`, `(hmem x).mp hx` in place of `(conjugateClosedSubgroup_mem K σ x).mp hx`, and `rw [hmem]` in place of `rw [conjugateClosedSubgroup_mem]`. Both images are now images of subgroups under `D.degree.toMonoidHom`, and `ext z` reduces the equality to two inclusions. If `x ∈ σ⁻¹ G_K σ`, then `k = σ x σ⁻¹ ∈ G_K` by `hmem`, and `simp [k, map_mul, mul_assoc]` shows `d(k) = d(x)`, since `ZHatMul` is commutative. Conversely, for `k ∈ G_K` the element `x = σ⁻¹ k σ` lies in `σ⁻¹ G_K σ` by `hmem` (after `simpa [x, mul_assoc]` simplifies `σ x σ⁻¹` to `k`), and `simp [x, map_mul, mul_assoc, mul_comm]` shows `d(x) = d(k)`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`, lines 31–51](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean#L31-L51):
the docstring at line 31 and the theorem at lines 32–51. It lies in `namespace ClassFormation` (line 17), with `open KummerTheory` (line 19), `open CyclicCohomology` (line 21), its `noncomputable section` (line 25) and the variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 28) and `{D : DegreeData G} {A : Rep ℤ G}` (line 29), which the theorem's own binders shadow and which it does not use. The source is:

```lean
/-- Conjugating an abstract field does not change its degree image. -/
theorem DegreeData.fieldImage_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (D : DegreeData G) (K : ClosedSubgroup G) (σ : G) :
    D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K := by
  rw [D.fieldImage_eq_map, D.fieldImage_eq_map]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    let k : K.toSubgroup :=
      ⟨σ * x * σ⁻¹, (conjugateClosedSubgroup_mem K σ x).mp hx⟩
    refine ⟨k.1, k.2, ?_⟩
    simp [k, map_mul, mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    let x : G := σ⁻¹ * k * σ
    have hx : x ∈ conjugateClosedSubgroup K σ := by
      rw [conjugateClosedSubgroup_mem]
      change σ * x * σ⁻¹ ∈ K.toSubgroup
      simpa [x, mul_assoc] using hk
    refine ⟨x, hx, ?_⟩
    simp [x, map_mul, mul_assoc, mul_comm]
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`;
its SHA-256 is `f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `DegreeData.fieldImage_conjugateStatement D K σ` as its type, and begin the proof with `show` stating it unfolded;
- state the published `...Statement`-typed M010.011 and M026.002 results unfolded as the local facts `hKσ`, `hK` and `hmem`, and rewrite with or apply these in place of the source's `D.fieldImage_eq_map` and `conjugateClosedSubgroup_mem`;
- omit `open KummerTheory`, `open CyclicCohomology`, the variable declarations and all other source declarations.

The theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M027.001. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
