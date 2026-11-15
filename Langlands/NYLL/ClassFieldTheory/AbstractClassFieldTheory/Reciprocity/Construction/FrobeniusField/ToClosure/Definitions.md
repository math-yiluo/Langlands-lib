# NYLL M016.021: the restriction from a Frobenius fixed field to the Frobenius closure

This file adapts one definition of Naganori Yamaguchi's
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
| M016.021 | 511, 512–534 | `frobeniusFixedFieldToClosure` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedFieldToClosure` |

The body uses the proofs of the source theorems M016.006
`frobeniusFixedField_le` (docstring line 100, statement lines 101–106,
proof lines 107–108) and M016.007 `extensionSubgroup_frobeniusFixedField`
(docstring lines 110–111, statement lines 112–120, proof lines 121–133), as
described below.

## The objects

Every object used is a published source definition or a Mathlib definition.
No replacement degree datum, field, inertia group, Frobenius lift, fixed
field or closure is introduced.

- `D : DegreeData G` (M010.002) is the source degree datum.
- `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field : ClosedSubgroup G` with finiteness of its residue quotient;
  `K.field.toSubgroup` is the group `G_K`.
- `L : ClosedSubgroup G` with `hLK : L.toSubgroup ≤ K.field.toSubgroup` is
  the extension. `L.toSubgroup.subgroupOf K.field.toSubgroup` is Mathlib's
  subgroup `G_L` of `G_K`; it is the exact body of the source abbreviation
  `extensionSubgroup K.field L hLK` (M004.002, published as the abbreviation
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`).
- `D.extensionInertiaWithin K.field L hLK` (M012.002) is the inertia
  subgroup `I_L` of `G_K`, and `G(\widetilde L|K)` is the quotient
  `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK`.
- `σ : D.FrobeniusElements K L hLK` (M012.009) is a Frobenius lift, an
  element `σ.1` of `G(\widetilde L|K)` of strictly positive natural
  normalized degree.
- `D.frobeniusClosure K L hLK σ` (M014.023) is the closed subgroup
  `Γ = closure ⟨σ.1⟩` of `G(\widetilde L|K)`.
- `D.frobeniusFixedSubgroupWithin K L hLK σ` (M016.001) is the subgroup
  `G_Σ ≤ G_K`, the inverse image of `Γ` under the quotient map
  `G_K → G(\widetilde L|K)`.
- `D.frobeniusFixedField K L hLK σ` (M016.004) is the field `Σ`, the closed
  subgroup of `G` whose underlying subgroup is the image of `G_Σ` under the
  inclusion `G_K → G`. Its membership is, by definition, the existence of
  `k : K.field.toSubgroup` with `k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ`
  and `k.1 = g`. These names are published in the module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions`,
  which is the single import here and transitively provides the others.
- `MonoidHom` (`→*`), `Subgroup.inclusion`, `QuotientGroup.mk`,
  `Subgroup.subgroupOf` and `Subtype.ext` are Mathlib's.

## Telescope

The declaration has the source section's implicit `G : Type*`, which
elaborates to `G : Type u_1` (source line 25; the source file has no
universe declaration), followed by `[Group G]` and `[TopologicalSpace G]`,
and then the binders below. No hypothesis is added or removed. The normality
binder is the source binder `[hLnormal : (extensionSubgroup K.field L hLK).Normal]`
with `extensionSubgroup` expanded.

```lean
def frobeniusFixedFieldToClosure (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup →*
      D.frobeniusClosure K L hLK σ
```

## Construction

`D.frobeniusFixedFieldToClosure K L hLK σ` (M016.021) is the group
homomorphism `G_Σ → Γ` that sends an element `s` of the subgroup underlying
`Σ` to the class in `G(\widetilde L|K)` of `s` regarded as an element of
`G_K`. Its `toFun` is built as follows.

1. A local hypothesis `hle` states
   `(D.frobeniusFixedField K L hLK σ).toSubgroup ≤ K.field.toSubgroup`, the
   statement of M016.006. It is proved by the source proof of M016.006: an
   element of `Σ` has the form `k.1` for some `k : K.field.toSubgroup`, and
   `k.2` is the required membership.
2. As in the source, `k : K.field.toSubgroup` is `Subgroup.inclusion hle s`,
   and the value is `⟨QuotientGroup.mk k, _⟩`.
3. A local hypothesis `hsub` states
   `(D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup = D.frobeniusFixedSubgroupWithin K L hLK σ`,
   the statement of M016.007 with `extensionSubgroup` expanded. It is proved
   by the source proof of M016.007: by extensionality, membership of `k` on
   the left is changed to `k.1 ∈ D.frobeniusFixedField K L hLK σ`, and this
   is changed to the existence statement above. If `t` is a witness with
   `t.1 = k.1` then `t = k` and the membership transfers; conversely `k`
   itself is a witness.
4. As in the source, `hk` states that `k` lies in
   `(D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup`,
   given by `s.2`. Rewriting `hk` with `hsub` gives
   `k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ`, which is by definition
   membership of `QuotientGroup.mk k` in `Γ`.

The fields `map_one'` and `map_mul'` are the source's: both values agree
with the source by `Subtype.ext` and `rfl`.

The value of the map on `s` is the class of the element `⟨s.1, _⟩` of
`G_K`. Only the proofs of the propositions `hle` and `hsub` differ in form
from the source, which uses the theorems M016.006 and M016.007; by proof
irrelevance the homomorphism is the source's.

## Modifications

Worker 5264 makes these modifications:

- Extract only M016.021, with the namespaces `ClassFormation` (line 17) and
  `DegreeData` (line 27), the noncomputable section (line 23) and the
  variable declaration (line 25). Replace the module documentation by one
  describing this declaration and the modifications. The source
  `open CyclicCohomology` (line 19) is omitted: here it serves only to
  resolve `extensionSubgroup`, which is expanded below.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
- Expand `extensionSubgroup K.field L hLK` (line 515) and
  `extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ) (D.frobeniusFixedField_le K L hLK σ)`
  (lines 524–525) to their exact Mathlib bodies
  `L.toSubgroup.subgroupOf K.field.toSubgroup` and
  `(D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup`,
  following the published sibling modules. The expressions are
  definitionally equal, since `extensionSubgroup` is an abbreviation with
  this body that does not use its proof argument.
- Replace the two applications `D.frobeniusFixedField_le K L hLK σ` (lines
  521 and 525) of the theorem M016.006 by the local hypothesis `hle`, proved
  by the source proof of M016.006 (lines 107–108). After the expansion
  above, the application in line 525 disappears.
- Replace the rewrite with the theorem M016.007 (line 526) by a rewrite
  with the local hypothesis `hsub`, proved by the source proof of M016.007
  (lines 121–133). In that proof, the source rewrite with the `rfl` lemma
  M016.005 `mem_frobeniusFixedField_iff` (line 125; statement lines 89–97,
  proof `rfl` line 98) becomes a `change` to the right-hand side of
  M016.005.
- Replace the source import `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField`
  with the published module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions`.
- The declaration name, docstring, the remaining telescope, the result
  type and the remaining body are unchanged.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The theorems M016.005, M016.006 and M016.007 are stated as proposition
targets in the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Statements`.
The source simp lemma M016.022 `frobeniusFixedFieldToClosure_apply` and the
other later declarations of the source file are not part of this
contribution. This definition discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
