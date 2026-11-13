# NYLL M024: relative coset action and norm-value statement targets

The paired Lean file adapts four theorem statements from Naganori
Yamaguchi's ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`,
SHA-256
`5d57e3b5f1941fc987fefea159ad4686bb5f934319d6662c436b917bdbbf8578`.
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

Every original name below has prefix `ClassFormation.` and every adapted
name has prefix `Langlands.NYLL.ClassFormation.`.

| Unit | Source name | Statement lines | Original proof lines | Adapted Prop definition |
| --- | --- | --- | --- | --- |
| M024.002 | `relativeCosetAction_mk` | 60–64 | 65 | `relativeCosetAction_mkStatement` |
| M024.004 | `leftMulCosetEquiv_mk` | 73–75 | 76 | `leftMulCosetEquiv_mkStatement` |
| M024.006 | `relativeCosetAction_add` | 88–95 | 96–99 | `relativeCosetAction_addStatement` |
| M024.008 | `relativeNormValue_fixed` | 114–120 | 121–136 | `relativeNormValue_fixedStatement` |

The enclosing source context is namespace `ClassFormation` (line 22),
the two namespace openings (lines 24–25), `noncomputable section`
(line 29) and the group variables at line 34.
Each theorem becomes a `def` returning `Prop`; its body is precisely the
original assertion after the namespace changes and abbreviation expansion
described below. The original proofs are separate obligations.

## Complete parameters and assertions

For the relative-action and norm-value targets, the initial telescope is
implicit `{G : IntegralRepGroupType}`, then `[Group G]` and
`[TopologicalSpace G]`, then explicit
`A : Rep ℤ G`, `K L : ClosedSubgroup G` and
`hLK : L.toSubgroup ≤ K.toSubgroup`, in that order.
The published `Langlands.NYLL.IntegralRepGroupType` is `Type 0`.
The representation carrier has an arbitrary universe, giving each
declaration one universe parameter. The topology is used only to form the
closed subgroups. There is no assumption of a topological group, profiniteness,
continuity of the representation or normality of the relative subgroup.

`relativeCosetAction_mkStatement` next has explicit
`a : ambientFixedAddSubgroup A L` and `k : K.toSubgroup`.
Its assertion is

```lean
relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1
```

It describes evaluation of the actual quotient lift on a representative.

`leftMulCosetEquiv_mkStatement` has its own complete telescope
`{G : Type u} [Group G] (H : Subgroup G) (g x : G)`.
The implicit group shadows the section group, so it has an unrestricted
universe and no topology parameter. Its assertion is

```lean
leftMulCosetEquiv H g (QuotientGroup.mk x) = QuotientGroup.mk (g * x)
```

It describes left multiplication on the actual left-coset quotient of an
arbitrary subgroup.

`relativeCosetAction_addStatement` takes, after the common initial telescope,
explicit `a b : ambientFixedAddSubgroup A L`, then explicit
`q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)`.
Its assertion is

```lean
relativeCosetAction A K L hLK (a + b) q =
  relativeCosetAction A K L hLK a q +
    relativeCosetAction A K L hLK b q
```

The addition is the actual additive-subgroup operation on the fixed elements
and the representation module addition on the result.

`relativeNormValue_fixedStatement` takes the instance
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`
after `hLK`, and then explicit
`a : ambientFixedAddSubgroup A L` and `k : K.toSubgroup`.
Its assertion is

```lean
A.ρ k.1 (relativeNormValue A K L hLK a) =
  relativeNormValue A K L hLK a
```

The finite instance precedes `a` and `k`, exactly as in the source.
The value is the sum over the actual relative quotient from the data
module. The assertion retains the particular group element `k` as a
parameter, rather than introducing a different fixedness predicate.

## Reused objects and modifications

The imported module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions`
supplies the adapted data from M024.001, .003 and .005. Their exact
constructions and source correspondence are documented in
[`Definitions.md`](Definitions.md). The source `ambientFixedAddSubgroup`
is the published
`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` from M023.001.

Source `CyclicCohomology.extensionSubgroup K L hLK` is expanded to its exact
body `L.toSubgroup.subgroupOf K.toSubgroup` in quotient binders and the
finite instance. This is source M004.002 in
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54,
SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`.
Its complete telescope is implicit
`{G : Type u} [Group G] [TopologicalSpace G]`,
then explicit `K L : ClosedSubgroup G` and
`_hLK : L.toSubgroup ≤ K.toSubgroup`. The last proof is unused in its
abbreviation body. The actual reused Mathlib declaration is
`Subgroup.subgroupOf`, at
`Mathlib/Algebra/Group/Subgroup/Map.lean`, lines 282–285, in the approved
Mathlib pin. Every original inclusion parameter remains in the targets.
A private focused check confirms the whole abbreviation with its complete
telescope against this body by `rfl`.

Worker 200 made the following adaptations on 13 November 2026:

1. Prefix the namespace by `Langlands.NYLL` and import the focused data module
   instead of the original four imports. `KummerTheory` resolves to the
   published namespaced support. Drop the unused `open CyclicCohomology`
   and `open scoped BigOperators`.
2. Expand `extensionSubgroup` by its exact body, with parentheses around
   the replacement term.
3. Convert each theorem into the listed Prop-valued `def` with its
   `Statement` suffix. Keep the source hypotheses, binder kinds and order,
   and the entire source assertion. Omit the proof bodies and the two
   source `simp` attributes, which belonged to proved equations.
4. Keep the source `noncomputable section`, replace the module introduction
   with an extraction notice, and adjust the declaration docstrings to
   identify them as targets. Omit the unrequested zero-action, norm
   homomorphism and later units.

There are no new instances or public helper declarations. In particular,
the source proof of M024.008 uses `leftMulCosetEquiv` for reindexing, but
that proof is not used to define this target.

## Development verification and scope

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Focused inspection of each of the four target declarations succeeds
and reports `statement_returns_prop = true`.

A separate private probe reconstructs the three original data definitions
and four assertion functions with the original relative-subgroup abbreviation
and verifies equality of all seven entire functions with their adapted
counterparts by `rfl`, using an arbitrary universe parameter. This checks
the dependent telescopes before application, not only selected instances.
The probe compiles with zero errors and warnings. Its type output confirms
the free carrier universe for the representation-based targets and the
arbitrary group universe for `leftMulCosetEquiv_mkStatement`.

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
