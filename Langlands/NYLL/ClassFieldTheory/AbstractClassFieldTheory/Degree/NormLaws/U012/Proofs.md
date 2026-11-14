# NYLL M026.012: the underlying element of the normal-extension action

`Langlands.NYLL.ClassFormation.normalExtensionAction_coe` proves the published
proposition `Langlands.NYLL.ClassFormation.normalExtensionAction_coeStatement` of
module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`.

## Statement

The parameters are, in order, the section group `{G : IntegralRepGroupType}`
(`Langlands.NYLL.IntegralRepGroupType` is `Type 0`), instances `[Group G]` and
`[TopologicalSpace G]`, and explicit `A : Rep ℤ G`, `K L : ClosedSubgroup G`,
`hLK : L.toSubgroup ≤ K.toSubgroup`, `hnormal : (extensionSubgroup K L hLK).Normal`,
`k : K.toSubgroup` and `a : ambientFixedAddSubgroup A L`. The one universe
parameter is that of the representation carrier, as in the target. The type of the
theorem is exactly `normalExtensionAction_coeStatement A K L hLK hnormal k a`, which
unfolds to

```lean
((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup A L) : A.V) =
  A.ρ k.1 a.1
```

The action `normalExtensionAction` (M026.011, module `...Degree.NormLaws.Definitions`)
of `k ∈ G_K` on the `G_L`-fixed vectors `A_L`, for `G_L` normal in `G_K`, has
underlying element `A.ρ k.1 a.1`.

## Implemented proof

The proof is the unchanged source term `rfl`. The published definition
`normalExtensionAction` is `refine ⟨A.ρ k.1 a.1, ?_⟩` followed by a proof that the
vector is `G_L`-fixed, so its first projection is definitionally `A.ρ k.1 a.1`. The
expected type `normalExtensionAction_coeStatement ...` is a definition that the
elaborator unfolds when checking `rfl`, so no `show` is needed.

The only direct import is `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`, which transitively supplies
`normalExtensionAction`, `ambientFixedAddSubgroup`, `extensionSubgroup` and
`IntegralRepGroupType`. The module opens `KummerTheory` (for
`ambientFixedAddSubgroup`) and `CyclicCohomology` (for `extensionSubgroup`) and
declares the source section variables `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G]`. The kernel axioms reported by inspection are `propext` and
`Quot.sound`; they enter through the imported definitions in the statement type.

## Source correspondence and modifications

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`, SHA-256
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`, retained
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Unit M026.012 is the theorem `ClassFormation.normalExtensionAction_coe`: docstring
lines 270–273, `@[simp]` attribute line 274, statement lines 275–281 and proof line
282, with the section variables of line 29 and the `open` lines 18 and 20. Worker
5014 extracts it into this focused module, prefixes the namespace with
`Langlands.NYLL`, replaces the source imports by the published statement module,
and writes the conclusion as the published target applied to the parameters. The
source `@[simp]` attribute is omitted: the theorem's type is now the Prop-valued
target rather than a syntactic equation, and the statement module records that the
simp attributes are not part of the port. The docstring, the section variables,
the parameter telescope and the proof term are the source ones; the source's
`noncomputable section` and `open scoped` line are not needed by this theorem.

This is an abstract subgroup-level fact of the NYLL abstract-field model. It
discharges no host class-formation, cup, transfer, Tate or reciprocity target.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim, and
the Lean module docstring records the modifications. The existing Library files
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
