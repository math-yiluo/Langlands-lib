# NYLL M301.001–.002: the unramified degree homomorphism and its kernel

Worker 114 adapts Naganori Yamaguchi’s `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean>),
lines 38–48 (two definitions with their docstrings), inside the source
context of lines 22–36 (`noncomputable section`, `namespace ClassFormation`,
`universe u`, `section DegreeOnly`,
`variable {G : Type u} [Group G] [TopologicalSpace G]`,
`namespace DegreeData`). The full original file has SHA-256
`29a3ec39fcabc17faa969f1c4c225a7cfd07555a00298e58daaa4b6fa6c7bb60`
(inventory module M301). The source is registered as
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

## Source correspondence

| Unit | Source line | Original declaration | Adapted declaration |
| --- | --- | --- | --- |
| M301.001 | 39 | `ClassFormation.DegreeData.unramifiedDegreeHom` | `Langlands.NYLL.ClassFormation.DegreeData.unramifiedDegreeHom` |
| M301.002 | 45 | `ClassFormation.DegreeData.unramifiedDegreeKernelWithin` | `Langlands.NYLL.ClassFormation.DegreeData.unramifiedDegreeKernelWithin` |

Both definitions have the complete source telescope: implicit
`{G : Type u}` (one universe variable `u`, not restricted to `Type 0`),
instance-implicit `[Group G]` and `[TopologicalSpace G]`, then explicit
`(D : DegreeData G)`, `(K : FiniteResidueAbstractField D)`, `(f : ℕ)` and
`(hf : 0 < f)`. Neither requires `IsTopologicalGroup G`.

- `unramifiedDegreeHom D K f hf : K.toSubgroup →ₜ* Multiplicative (ZMod f)`
  is exactly `(zHatReductionMul f hf).comp (D.normalizedDegree K)`: the
  continuous normalized degree `d_K : G_K → ℤ̂` (in its multiplicative
  presentation `ZHatMul`) followed by the continuous reduction
  `ℤ̂ → ℤ/fℤ`, again multiplicatively. Its domain is the actual subgroup
  `K.toSubgroup` (definitionally `K.field.toSubgroup`) of the actual
  finite-residue abstract field with its subspace topology.
- `unramifiedDegreeKernelWithin D K f hf : Subgroup K.toSubgroup` is exactly
  the kernel `(unramifiedDegreeHom D K f hf).toMonoidHom.ker`, a subgroup of
  the field subgroup itself (not of `G`).

| Source dependency | Published declaration reused | Module |
| --- | --- | --- |
| `ClassFormation.DegreeData` (M010) | `Langlands.NYLL.ClassFormation.DegreeData` | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions` |
| `ClassFormation.DegreeData.FiniteResidueAbstractField`, `.toSubgroup` (M010.021–.025) | `Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField`, `.toSubgroup` | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions` |
| `ClassFormation.zHatReductionMul` (M014.009) | `Langlands.NYLL.ClassFormation.zHatReductionMul` | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U009.Definitions` |
| `ClassFormation.DegreeData.normalizedDegree` (M011.006) | `Langlands.NYLL.ClassFormation.DegreeData.normalizedDegree` | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions` |

The published `normalizedDegree` (accepted artifact
`48af3009-2623-48e2-bb5b-f3e19e008f8b`) has the source signature
`(D : DegreeData G) (K : FiniteResidueAbstractField D) :
K.field.toSubgroup →ₜ* ZHatMul` over `{G : Type*} [Group G]
[TopologicalSpace G]`, so it applies to the `Type u` telescope here without
change.

## Modifications

All modifications are by Worker 114.

- The namespace `ClassFormation` is prefixed with `Langlands.NYLL`.
- Only M301.001–.002 are extracted. The remaining M301 commands (the closed
  subgroup `unramifiedExtensionOfDegree`, the finite Galois/abelian factors,
  the `Representation` section and all theorems) are omitted; the three
  theorem targets M301.003, .004 and .009 are in the sibling `Statements`
  module, and the others belong to later tasks.
- The source imports (`Degree.FrobeniusFixedField`,
  `Reciprocity.FiniteAbelianSubextension`, `Reciprocity.NormTopology`) are
  replaced by the two focused published modules providing
  `normalizedDegree` and `zHatReductionMul`.
- The unused source openings `open scoped Topology` and
  `open ClassFormation CyclicCohomology KummerTheory` are omitted; no name
  in the extracted bodies resolves through them.
- The source `noncomputable section`, `universe u`, `section DegreeOnly`,
  section variables, parameter order, binder kinds, docstrings and bodies are
  retained verbatim. No instance, attribute or `simp` lemma is introduced.

Exact-name search of the Library found no previously published declaration
for either unit, and Mathlib has no construction specific to this degree
datum; the generic Mathlib pieces (`ContinuousMonoidHom.comp`,
`MonoidHom.ker`) are used exactly as in the source.

This is a data-definition candidate. It claims no theorem: the kernel
equation, closedness and surjectivity are only stated, in the sibling
`Statements` module, and no fixed field, unramified extension or
reciprocity result is asserted.

## License

The original copyright and author header is retained verbatim. The port
remains under Apache-2.0; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, already published in the Library and unchanged.
