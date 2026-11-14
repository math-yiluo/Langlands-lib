# NYLL M039: the maximal-unramified norm subgroup and the finite norm quotient — statement targets

The paired Lean file adapts two theorem statements from Naganori Yamaguchi's
ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`,
SHA-256
`f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7`.
The source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project notes.

## Source correspondence

| Unit | Source name | Statement lines | Original proof lines | Adapted Prop definition |
| --- | --- | --- | --- | --- |
| M039.019 | `ClassFormation.DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup` | 254–261 (docstring 254–255) | 262–265 | `Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroupStatement` |
| M039.020 | `ClassFormation.DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker` (`private theorem`) | 267–272 (no docstring) | 273–275 | `Langlands.NYLL.PortInternal.M039.d020Statement` |

The enclosing source context is `namespace ClassFormation` (line 20),
`open KummerTheory` (line 22), `open CyclicCohomology` (line 24),
`noncomputable section` (line 28), `section quotientMaps` (line 247), the
group variables at line 250 and `namespace DegreeData` (line 252). Each
theorem becomes a `def` returning `Prop` whose binders are the source
hypotheses in source order, with the same binder kinds and names, and whose
body is the source conclusion, after the namespace change and abbreviation
expansion below. Because the source M039.020 is `private`, it receives the
`Langlands.NYLL.PortInternal.M039.d020Statement` name required by the task
for private source commands; it is declared at the source position with a
`_root_` prefix, so its body is elaborated in the same namespace
`Langlands.NYLL.ClassFormation.DegreeData` as the source. The original
proofs are separate obligations.

## Complete parameters and assertions

Both targets have the same telescope: implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]` (`IntegralRepGroupType` is `Type 0`;
the representation carrier universe is the single level parameter), then
explicit `D : DegreeData G`, `A : Rep ℤ G`, `K L : ClosedSubgroup G`,
`hLK : L.toSubgroup ≤ K.toSubgroup`, and the named instance binder
`[hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`.
The instance `hfinite` is used by instance search in each assertion, where
it supplies the finiteness argument of `finiteNormSubgroup` and
`finiteNormClassHom`.

- `DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroupStatement`:
  assertion
  `D.maximalUnramifiedNormSubgroup A K L ≤ finiteNormSubgroup A K L hLK`,
  an inequality of additive subgroups of `ambientFixedAddSubgroup A K`. In
  the abstract model it states that the norm subgroup
  `N_{\widetilde L|K} A_{\widetilde L}` of the maximal unramified field
  attached to `L`, the intersection of the norm images from its finite
  intermediate fields, is contained in the single norm image `N_{L|K} A_L`.
- `PortInternal.M039.d020Statement`: assertion
  `D.maximalUnramifiedNormSubgroup A K L ≤ (finiteNormClassHom A K L hLK).ker`,
  i.e. the same subgroup is killed by the class map
  `A_K → A_K / N_{L|K} A_L`.

## Reused objects and modifications

The imports supply published data by Lean name:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`:
  `finiteNormSubgroup` (M039.001, source lines 35–40) and
  `finiteNormClassHom` (M039.005, source lines 75–82), with their source
  telescopes and bodies, together with `relativeNorm` and
  `ambientFixedAddSubgroup`; see its paired `Definitions.md`.
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions`:
  `DegreeData.maximalUnramifiedNormSubgroup` (M029.024, published by
  Worker 5264), the source definition
  `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
  lines 292–296 (SHA-256
  `7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`),
  whose body is `infiniteNormSubgroup A (D.maximalUnramifiedField L) K`;
  `DegreeData` and `maximalUnramifiedField` come from the published
  `NormSubgroup.Definitions` it imports.

Source `CyclicCohomology.extensionSubgroup K L hLK` (M004.002,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54,
SHA-256 `06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`)
is an abbreviation with body `L.toSubgroup.subgroupOf K.toSubgroup`; its
occurrence in each instance binder is replaced by that exact Mathlib term,
in parentheses. The inclusion parameter `hLK` remains in both telescopes.

Worker 96 made only the following adaptations on 14 November 2026:

1. Prefix the namespace by `Langlands.NYLL`; import the two focused
   published modules instead of the original imports. Drop the unused
   `open CyclicCohomology` and `universe u`.
2. Expand `extensionSubgroup` by its exact body, with parentheses.
3. Convert M039.019 into a Prop-valued `def` with the `Statement` suffix and
   the private M039.020 into the Prop-valued `def`
   `Langlands.NYLL.PortInternal.M039.d020Statement`, keeping every source
   hypothesis, binder kind, binder name and order and the entire
   conclusion. Omit the proofs.
4. Keep `noncomputable section`, `section quotientMaps` and
   `namespace DegreeData`, replace the module introduction with an
   extraction notice, mark the M039.019 docstring as a target and add a
   docstring naming the private source theorem for M039.020.

The source proofs use the theorem
`DegreeData.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup`, the
definition `DegreeData.fieldAsMaximalUnramifiedIntermediate` and
`finiteNormClass_eq_zero_iff`; these are not needed by the statements and
are not ported here. No instance or helper declaration is introduced.

## Development verification and scope

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Focused inspection of each of the
two targets succeeds and reports `statement_returns_prop = true`, with
axioms `propext`, `Classical.choice` and `Quot.sound`.

A private probe restates the two source assertions with the original
`[hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]` binder
over the published data and verifies equality of each entire dependent
function with the adapted target by `rfl` at an arbitrary universe; it also
checks by `rfl` that `D.maximalUnramifiedNormSubgroup A K L` is
`infiniteNormSubgroup A (D.maximalUnramifiedField L) K`. The probe supplies
no public declaration.

These are statement targets in the NYLL abstract-field model; their proofs
belong to separate `lean.proof@1` tasks after publication. The host
class-formation, cup, transfer, Tate and reciprocity obligations remain with
their existing owners.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim.
The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean modification notice and this Markdown identify every adaptation.
