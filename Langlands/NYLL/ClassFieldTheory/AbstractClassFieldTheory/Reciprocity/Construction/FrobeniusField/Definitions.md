# NYLL M016.001 and M016.004: the field fixed by a Frobenius lift

This file adapts two definitions of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`707b3783859e0c991b0a4e5a3a5c014c808617f79587d1895e49787a26d1ca10`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines (docstring, declaration) | Original name after `ClassFormation.DegreeData.` | Adapted name |
| --- | --- | --- | --- |
| M016.001 | 29–30, 31–37 | `frobeniusFixedSubgroupWithin` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedSubgroupWithin` |
| M016.004 | 69–71, 72–85 | `frobeniusFixedField` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField` |

The closedness proof inside M016.004 uses the proof of the source theorem
M016.003 `frobeniusFixedSubgroupWithin_isClosed` (docstring line 53,
statement lines 54–61, proof lines 62–67), as described below.

## The objects

Every object used is a published source definition or a Mathlib definition.
No replacement degree datum, field, inertia group, Frobenius semigroup or
generated subgroup is introduced.

- `D : DegreeData G` (M010.002) is the source degree datum.
- `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field : ClosedSubgroup G` with finiteness of its residue quotient;
  `K.field.toSubgroup` is the group `G_K`.
- `L : ClosedSubgroup G` (Mathlib's closed subgroups) with
  `hLK : L.toSubgroup ≤ K.field.toSubgroup` is the extension.
  `L.toSubgroup.subgroupOf K.field.toSubgroup` is Mathlib's subgroup `G_L`
  of `G_K`. It is the exact body of the source abbreviation
  `extensionSubgroup K.field L hLK` (M004.002, published as the abbreviation
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`), and the published
  sibling modules use it in the same way.
- `D.extensionInertiaWithin K.field L hLK` (M012.002) is the inertia
  subgroup `I_L = G_L ⊓ D.fieldInertiaWithin K.field` of `G_K`; it is normal
  when `G_L` is normal (instance M012.003). `G(\widetilde L|K)` is the
  quotient `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK`.
- `σ : D.FrobeniusElements K L hLK` (M012.009) is a Frobenius lift: an
  element `σ.1` of `G(\widetilde L|K)` whose normalized degree is a strictly
  positive natural number.
- `D.frobeniusClosure K L hLK σ` (M014.023) is the closed subgroup
  `Γ = closure ⟨σ.1⟩` of `G(\widetilde L|K)`. It is published in the module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`
  (submitted together with this module), which is the single import here and
  transitively provides the other names.
- `QuotientGroup.mk'`, `Subgroup.comap`, `Subgroup.map`,
  `Subgroup.subtype`, `ClosedSubgroup`, `continuous_quotient_mk'`,
  `IsClosed.preimage` and `IsClosed.isClosedEmbedding_subtypeVal` are
  Mathlib's.

## Telescopes

Both declarations have the source section's implicit `G : Type*`, which
elaborates to `G : Type u_1` (source line 25; the source file has no universe
declaration), followed by `[Group G]` and `[TopologicalSpace G]`, and then
the explicit and instance binders below. No hypothesis is added. The
normality binder `[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]`
is the source binder `[hLnormal : (extensionSubgroup K.field L hLK).Normal]`
with `extensionSubgroup` expanded.

```lean
def frobeniusFixedSubgroupWithin (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Subgroup K.field.toSubgroup

def frobeniusFixedField (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : ClosedSubgroup G
```

## Constructions

`D.frobeniusFixedSubgroupWithin K L hLK σ` (M016.001) is the subgroup
`G_Σ ≤ G_K`: the inverse image
`(D.frobeniusClosure K L hLK σ).toSubgroup.comap (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))`
of `Γ` under the quotient homomorphism `G_K → G(\widetilde L|K)`. The body is
the source's.

`D.frobeniusFixedField K L hLK σ` (M016.004) is the abstract field `Σ`
fixed by `σ`, as a closed subgroup of the ambient group `G`. Its underlying
subgroup is the image
`(D.frobeniusFixedSubgroupWithin K L hLK σ).map K.field.toSubgroup.subtype`
of `G_Σ` under the inclusion `G_K → G`; this field is the source's. Its
closedness field is proved in two steps:

1. A local hypothesis `hclosed` states that `G_Σ` is closed in `G_K`. It is
   proved exactly by the source proof of M016.003: the goal is changed to
   closedness of the preimage of the closed set `Γ` under the quotient map,
   which follows from `(D.frobeniusClosure K L hLK σ).isClosed'.preimage continuous_quotient_mk'`.
2. As in the source, the goal is changed to closedness of the image
   `Subtype.val '' G_Σ`, which follows because the inclusion of the closed
   subgroup `K.field` is a closed embedding:
   `K.field.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _ hclosed`.

## Modifications

Worker 5264 makes these modifications:

- Extract only M016.001 and M016.004, with the namespaces `ClassFormation`
  (line 17) and `DegreeData` (line 27), the noncomputable section (line 23)
  and the variable declaration (line 25). Narrow the module documentation to
  these declarations. The source `open CyclicCohomology` (line 19) is
  omitted: in the extracted declarations it serves only to resolve
  `extensionSubgroup`, which is expanded below.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
- Expand `extensionSubgroup K.field L hLK` to its exact Mathlib body
  `L.toSubgroup.subgroupOf K.field.toSubgroup` in both normality binders,
  following the published sibling modules. The two expressions are
  definitionally equal, since `extensionSubgroup` is an abbreviation with
  this body.
- In the closedness proof of M016.004, the source term
  `(D.frobeniusFixedSubgroupWithin_isClosed K L hLK σ)` (line 85), an
  application of the theorem M016.003, is replaced by the local hypothesis
  `hclosed`, proved by the source proof of M016.003 (lines 62–67) for the
  same statement. The change affects only the proof of the proposition
  `IsClosed`, so the closed subgroup is the source's. The theorem M016.003
  itself is stated as a target in the sibling Statements module.
- Replace the source import `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField`
  with the published module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`.
- The declaration names, docstrings, remaining telescopes, result types and
  the remaining construction bodies are unchanged.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The source theorems M016.002, M016.003, M016.005–M016.010 and
M016.012–M016.014 are stated as proposition targets in the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements`.
The source definition M016.011 `frobeniusFixedFiniteExtension`, whose body
uses the proofs of M016.006 and M016.010, and the later declarations of the
source file are not part of this contribution. These definitions discharge
no host class-formation, cup, transfer, Tate or reciprocity target.

## Verification

The module and its sibling Statements module passed a project Lean service
check on 15 November 2026 with environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
