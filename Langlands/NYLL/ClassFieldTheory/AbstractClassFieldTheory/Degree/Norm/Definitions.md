# NYLL M024: relative coset action, coset equivalence and norm-value data

This file adapts three definitions from Naganori Yamaguchi's ClassFieldTheory,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`.
The source file SHA-256 is
`5d57e3b5f1941fc987fefea159ad4686bb5f934319d6662c436b917bdbbf8578`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project notes.

## Source correspondence

Each source name in this table begins with `ClassFormation.`; each adapted
name begins with `Langlands.NYLL.ClassFormation.`.

| Unit | Source name | Source declaration lines | Adapted name |
| --- | --- | --- | --- |
| M024.001 | `relativeCosetAction` | 39–56 | `relativeCosetAction` |
| M024.003 | `leftMulCosetEquiv` | 68–70 | `leftMulCosetEquiv` |
| M024.005 | `relativeNormValue` | 79–85 | `relativeNormValue` |

The enclosing source context is `namespace ClassFormation` (line 22),
`open KummerTheory` (line 24), `open CyclicCohomology` (line 25),
`noncomputable section` (line 29), `open scoped BigOperators` (line 31) and
the group variables at line 34. The three declaration docstrings at
lines 36–38, 67 and 78 are retained verbatim.

## Objects and complete telescopes

The first and third definitions have the source's implicit
`{G : IntegralRepGroupType}`, followed by `[Group G]` and
`[TopologicalSpace G]`. The published
`Langlands.NYLL.IntegralRepGroupType` is exactly `Type 0`.
The representation `A : Rep ℤ G` has an arbitrary carrier universe, so each
of these declarations has one universe parameter for that carrier.
The acting group remains in universe zero.

`relativeCosetAction` then takes, explicitly and in order,
`A : Rep ℤ G`, `K L : ClosedSubgroup G`,
`hLK : L.toSubgroup ≤ K.toSubgroup`,
`a : ambientFixedAddSubgroup A L` and
`q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)`.
Its result is in the actual ambient representation module `A.V`.
The fixed subgroup is the published
`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` from M023.001:
its elements are those fixed by every element of `L.toSubgroup`.

The construction is the source `Quotient.liftOn'`, with representative
function `fun k : K.toSubgroup => A.ρ k.1 a.1`. The embedded
well-definedness proof is retained. For related representatives `x,y`,
it uses `QuotientGroup.leftRel_apply.mp` to obtain
`x⁻¹ * y` in the relative subgroup. It constructs
`l : L.toSubgroup` from that membership and proves
`y = x * ⟨l.1, hLK l.2⟩` by `Subtype.ext` and `simp [l]`.
It then rewrites by this equality, `map_mul` and `a.2 l`.
Thus the inclusion proof `hLK` remains an explicit argument and is used
inside the construction even though the subgroup expression itself
does not need it.

`leftMulCosetEquiv` has a different complete telescope:
`{G : Type u} [Group G] (H : Subgroup G) (g : G)`.
Its group shadows the section group, as in the source. It is universe
polymorphic, with no topology parameter. The result is the equivalence
`(G ⧸ H) ≃ (G ⧸ H)` and its complete body is the source
`MulAction.toPerm g`, using Mathlib's action of `G` by left multiplication
on left cosets. This requires an arbitrary subgroup, with no normality
hypothesis.

`relativeNormValue` takes the same initial implicit group and instances,
then explicit `A`, `K`, `L` and `hLK`, followed by the instance argument
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`,
then explicit `a : ambientFixedAddSubgroup A L`, in that order.
Its result is in `A.V`. Its source body is preserved:
it installs `Fintype.ofFinite` for that actual quotient and returns
`∑ q, relativeCosetAction A K L hLK a q`. It neither changes the quotient
to a chosen transversal nor requires a normal extension. Fixedness under
`K` is a separate statement target in `Norm/Statements.lean`.

## Reuse of the relative subgroup

Source M004.002,
`CyclicCohomology.extensionSubgroup`, is defined at lines 47–54 of
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean` at the same pin.
That file has SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`.
Its complete telescope is

```lean
{G : Type u} [Group G] [TopologicalSpace G]
(K L : ClosedSubgroup G) (_hLK : L.toSubgroup ≤ K.toSubgroup)
```

and its complete abbreviation body is
`L.toSubgroup.subgroupOf K.toSubgroup`.
Every occurrence of `extensionSubgroup K L hLK` in the paired file is
replaced by this exact body, as directed by Task 5819. The reused declaration
is Mathlib's `Subgroup.subgroupOf`, defined by comapping along the base
subgroup's inclusion in `Mathlib/Algebra/Group/Subgroup/Map.lean`,
lines 282–285, at the approved Mathlib pin. The inclusion hypothesis
remains in every source telescope; the source abbreviation ignores it.

A private focused Lean check reconstructs the abbreviation with this
entire telescope and verifies its whole function against
`Subgroup.subgroupOf` by `rfl`. It then reconstructs the three source
definitions with the abbreviation in place and verifies equality of each
entire adapted function with its source-shaped counterpart by `rfl`,
at an arbitrary universe parameter, before application to any arguments.
This checks the complete dependent telescopes as well as the constructions.
The private probe is development evidence and supplies no public declaration.

## Modifications and verification

Worker 200 made only the following adaptations on 13 November 2026:

1. Prefix `ClassFormation` by `Langlands.NYLL`. The unqualified
   `KummerTheory` and `IntegralRepGroupType` consequently resolve to the
   published names in that namespace.
2. Retain both source Mathlib imports. Replace the two original NYLL imports
   by the focused published
   `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`,
   which also imports the published `IntegralRepUniverse`.
3. Expand the `extensionSubgroup` abbreviation exactly as described above,
   with parentheses around the replacement expressions. Drop the unused
   `open CyclicCohomology`.
4. Extract only the three listed definitions, leaving the intervening theorem
   statements to the paired statement module and later source units to their
   own tasks. Replace the module introduction with the extraction and
   modification notice.

The source `noncomputable section`, `BigOperators` scope, binder kinds,
instance order, declaration bodies and embedded proof steps are preserved
subject only to the named abbreviation expansion. No instance is introduced.
The supporting fixed subgroup and universe alias are imported by Lean name;
the degree-data `FiniteResidueAbstractField.toSubgroup` is not used.

The draft compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The complete-function comparison
probe also compiles with zero errors and warnings. Type output confirms
the free representation carrier universe and the unrestricted universe
of `leftMulCosetEquiv`. Independent semantic review and publication
remain separate from these development checks.

This support data is internal to the NYLL abstract-field model. Its
subsequent norm homomorphism and theorem proofs are separate work, as are
the host class-formation, cup, transfer, Tate and reciprocity obligations.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim.
The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 200's modifications are recorded in the Lean header and above.
