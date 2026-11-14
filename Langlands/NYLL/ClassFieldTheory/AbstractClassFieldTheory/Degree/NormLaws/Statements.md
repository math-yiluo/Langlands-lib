# NYLL M026: conjugate closed subgroup, absolute extension, normal-extension action and tower finiteness statement targets

The paired Lean file adapts four theorem statements from Naganori
Yamaguchi's ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`,
SHA-256
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`.
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

Source names begin with `ClassFormation.`. Adapted names begin with
`Langlands.NYLL.ClassFormation.`, except the target of the private source
theorem, whose adapted name is given in full.

| Unit | Source name | Statement lines | Original proof lines | Adapted Prop definition |
| --- | --- | --- | --- | --- |
| M026.002 | `conjugateClosedSubgroup_mem` | 51–54 | 55–58 | `conjugateClosedSubgroup_memStatement` |
| M026.006 | `mem_absoluteExtension` (private) | 105–109 | 110 | `Langlands.NYLL.PortInternal.M026.d006Statement` |
| M026.012 | `normalExtensionAction_coe` | 275–281 | 282 | `normalExtensionAction_coeStatement` |
| M026.014 | `relativeTowerQuotientFinite` | 316–324 | 325–328 | `relativeTowerQuotientFiniteStatement` |

The source docstrings are at lines 47–49 (M026.002), 270–273 (M026.012)
and 315 (M026.014); M026.006 has none. M026.002 and M026.012 carry `@[simp]`
(lines 50 and 274). The enclosing source context is `namespace
ClassFormation` (line 16), `open KummerTheory` (line 18),
`open CyclicCohomology` (line 20), `noncomputable section` (line 24),
`open scoped BigOperators Pointwise` (line 26) and the section variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 29).
This context is reproduced in the paired Lean file.

Each theorem becomes a `def` returning `Prop`. Its parameters are the
complete source telescope in the source order and binder kinds, and its body
is exactly the source assertion. The source proofs are separate obligations.

## Complete parameters and assertions

### M026.002 `conjugateClosedSubgroup_memStatement`

The telescope is `{G : Type*} [Group G] [TopologicalSpace G]
[ContinuousMul G] (K : ClosedSubgroup G) (σ x : G)`. The group binder shadows
the section group, as in the source, so the target has one free universe.
The assertion is

```lean
x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K
```

It states that the conjugate closed subgroup is `σ⁻¹ K σ`, membership being
that of Mathlib's `ClosedSubgroup`.

### M026.006 `Langlands.NYLL.PortInternal.M026.d006Statement`

The telescope is `{G : Type*} [Group G] [TopologicalSpace G]
(K : ClosedSubgroup G) (x : (baseField G).toSubgroup)`, with a free universe.
The assertion is

```lean
x ∈ extensionSubgroup (baseField G) K (le_baseField K) ↔ x.1 ∈ K
```

Here `baseField G` is the published M010.003, the closed subgroup `⊤`, and
`le_baseField K : K.toSubgroup ≤ (baseField G).toSubgroup` is the published
theorem M010.005 in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`,
which is imported for this purpose. The target says that an element of the
absolute subgroup lies in the relative subgroup of `K` over the base field
exactly when its underlying element lies in `K`.

### M026.012 `normalExtensionAction_coeStatement`

The telescope is the section group `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G]`, then explicit `A : Rep ℤ G`,
`K L : ClosedSubgroup G`, `hLK : L.toSubgroup ≤ K.toSubgroup`,
`hnormal : (extensionSubgroup K L hLK).Normal`, `k : K.toSubgroup` and
`a : ambientFixedAddSubgroup A L`, in that order. The published
`Langlands.NYLL.IntegralRepGroupType` is `Type 0`; the representation
carrier universe is the target's one universe parameter. The assertion is

```lean
((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup A L) : A.V) =
  A.ρ k.1 a.1
```

It identifies the underlying element of `A.V` of the action defined in
`NormLaws/Definitions.lean`.

### M026.014 `relativeTowerQuotientFiniteStatement`

The telescope is `{G : Type*} [Group G] [TopologicalSpace G]
(K L M : ClosedSubgroup G) (hML : M.toSubgroup ≤ L.toSubgroup)
(hLK : L.toSubgroup ≤ K.toSubgroup)`, then the two instance arguments
`[Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]` and
`[Finite (L.toSubgroup ⧸ extensionSubgroup L M hML)]`, in that order, with a
free universe. The assertion is

```lean
Finite (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK))
```

that is, finiteness of relative coset spaces passes to the composite of a
tower of closed subgroups. The adapted M026.015 `totalExtension` in the data
module uses the source proof term of this theorem directly, so it does not
depend on this target or on its later proof.

## Reused objects and modifications

The imported module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`
supplies the adapted data `conjugateClosedSubgroup` (M026.001) and
`normalExtensionAction` (M026.011), documented in
[`Definitions.md`](Definitions.md). `extensionSubgroup` is the published
abbreviation `Langlands.NYLL.CyclicCohomology.extensionSubgroup`
(source M004.002, body `L.toSubgroup.subgroupOf K.toSubgroup`), used by name.
`ambientFixedAddSubgroup` is the published
`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (M023.001).

Worker 165 made the following adaptations on 14 November 2026:

1. Prefix the namespace by `Langlands.NYLL`, and replace the source imports
   by the data module and the published `Fields.U005.Proofs` module for
   `le_baseField`.
2. Name the target of the private source theorem
   `Langlands.NYLL.PortInternal.M026.d006Statement`, declared from inside the
   namespace with a `_root_` prefix.
3. Convert each theorem into the listed Prop-valued `def` with the
   `Statement` suffix, keeping the source hypotheses, binder kinds and order,
   and the entire source assertion. Omit the proof bodies and the two source
   `simp` attributes, which belong to proved equations.
4. Replace the declaration docstrings by docstrings that identify each
   declaration as a target and state its assertion, add one for the private
   target, and replace the module introduction with an extraction notice.
   The other theorems of the source module are not part of this task.

There are no new instances and no public helper declarations.

## Development verification and scope

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Inspection of each of the four
target declarations succeeds and reports `statement_returns_prop = true`.

A private probe checks that the source proofs prove the targets unchanged:
the `change`/`rw`/`simp only` proof for M026.002, `Iff.rfl` for M026.006,
`rfl` for M026.012, and the `Finite.of_equiv` term with
`Subgroup.quotientTowerEquiv` for M026.014. The probe supplies no public
declaration.

These are statement targets in the NYLL abstract-field model. Their proofs
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
