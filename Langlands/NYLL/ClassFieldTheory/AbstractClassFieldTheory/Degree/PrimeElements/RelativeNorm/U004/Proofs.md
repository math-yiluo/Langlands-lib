# NYLL M028.004: the relative norm of the trivial extension

`Langlands.NYLL.ClassFormation.relativeNorm_self` proves the published
proposition `Langlands.NYLL.ClassFormation.relativeNorm_selfStatement` of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.RelativeNorm.Statements`.

## Statement

The parameters are, in order, the section variables implicit
`G : IntegralRepGroupType` with instances `[Group G]` and `[TopologicalSpace G]`,
explicit `A : Rep ℤ G` and `K : ClosedSubgroup G`, the instance
`[Finite (K.toSubgroup ⧸ (K.toSubgroup.subgroupOf K.toSubgroup))]`, and explicit
`a : ambientFixedAddSubgroup A K`. The finiteness binder is written exactly as in
the published statement, through the `Subgroup.subgroupOf` body of the source's
`extensionSubgroup K K le_rfl`. The type of the theorem is exactly
`relativeNorm_selfStatement A K a`, which unfolds to

```lean
relativeNorm A K K le_rfl a = a
```

In words: the relative norm of the trivial extension `K | K` is the identity on
the `G_K`-fixed submodule `A_K`.

## Implemented proof

The module contains three declarations: two private local helpers and the
target.

1. `relativeNormApplyCoeLocal` (private) states
   `((relativeNorm A K L hLK a : ambientFixedAddSubgroup A K) : A.V) =
   relativeNormValue A K L hLK a` and is proved by `rfl`. It is a local copy of
   the source simp lemma `relativeNorm_apply_coe` (M024.010), whose published
   statement has no published proof yet; it is private and has a different
   name, so no second copy of M024.010 is published. It holds definitionally
   because the `toFun` of the published `relativeNorm` is
   `⟨relativeNormValue A K L hLK a, _⟩`.
2. `relativeCosetActionMkLocal` (private) states
   `relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1` and is
   the published proof `relativeCosetAction_mk A K L hLK a k` (M024.002, module
   `...Degree.Norm.U002.Proofs`) read at its unfolded type. The published
   theorem has the opaque type `relativeCosetAction_mkStatement A K L hLK a k`,
   which `rw` cannot use as an equation.
3. `relativeNorm_self` (the target). A `show` states the unfolded statement and
   `Subtype.ext` reduces it to an equality in `A.V`. The proof fixes
   `Fintype.ofFinite` on `K ⧸ extensionSubgroup K K le_rfl` and proves that
   every coset term equals `a.1`: by `Quotient.inductionOn'` it suffices to
   treat a representative `k`, for which `relativeCosetActionMkLocal` rewrites
   the term to `A.ρ k.1 a.1`, equal to `a.1` because `a` is `G_K`-fixed
   (`a.2 k`). It then unfolds the norm by `relativeNormApplyCoeLocal` and
   `relativeNormValue`, rewrites the summands by that equality (`simp_rw`) and
   evaluates the constant sum by `Finset.sum_const` and `Finset.card_univ`. It
   proves `extensionSubgroup K K le_rfl = ⊤` by `change` to
   `K.toSubgroup.subgroupOf K.toSubgroup = ⊤` and `Subgroup.subgroupOf_self`,
   deduces that the quotient has `Fintype.card` equal to `1` by
   `Nat.card_eq_fintype_card`, `Subgroup.index_eq_card` and
   `Subgroup.index_top`, and closes the goal by `one_nsmul`.

Imports: the required statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.RelativeNorm.Statements`,
the published proof module of `relativeCosetAction_mk`
(`...Degree.Norm.U002.Proofs`, M024.002), and the published module
`Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
which defines `extensionSubgroup` (an `abbrev` for
`L.toSubgroup.subgroupOf K.toSubgroup` in namespace
`Langlands.NYLL.CyclicCohomology`, opened as in the source). Because it is an
`abbrev`, the statement's finiteness instance on
`K.toSubgroup ⧸ (K.toSubgroup.subgroupOf K.toSubgroup)` serves for the
`extensionSubgroup K K le_rfl` quotients in the proof. The other published
declarations used are `relativeNorm`, `relativeNormValue`,
`relativeCosetAction` and `ambientFixedAddSubgroup`; the Mathlib lemmas used are
`Finset.sum_const`, `Finset.card_univ`, `Subgroup.subgroupOf_self`,
`Nat.card_eq_fintype_card`, `Subgroup.index_eq_card`, `Subgroup.index_top` and
`one_nsmul`. The kernel axioms reported by inspection are `propext`,
`Classical.choice` and `Quot.sound`.

## Source correspondence and modifications

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`,
SHA-256 `9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`,
retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Source name | Source lines | Port |
| --- | --- | --- | --- |
| M028.004 | `ClassFormation.relativeNorm_self` | docstring 77, `@[simp]` 78, theorem 79–105 | the target theorem, without `@[simp]` |

The enclosing source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (18), `open CyclicCohomology` (20), `noncomputable section`
(24) and the section variable line 27; the port keeps this context under the
namespace prefix `Langlands.NYLL`. The source section variables
`{D : DegreeData G} {A : Rep ℤ G}` (line 28) are not used by the theorem and are
omitted.

Modifications, all by Worker 735:

- The namespace is prefixed with `Langlands.NYLL`; the source import is
  replaced by the three published modules listed above.
- The conclusion is written as the published `relativeNorm_selfStatement A K a`,
  and the proof opens with a `show` of its unfolded form, which is the source
  statement. The finiteness binder is written through the `subgroupOf` body, as
  in the published statement.
- The source `@[simp]` attribute is omitted, since the conclusion is an opaque
  proposition rather than an equation.
- The source rewrites by the simp lemmas `relativeCosetAction_mk` and
  `relativeNorm_apply_coe` use the private local lemmas described above. All
  other proof steps are the source ones.

This is an abstract coset-sum identity of the NYLL abstract-field model. It
discharges no host class-formation, cup, transfer, Tate or reciprocity target.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim, and
the Lean module docstring records the modifications. The existing Library files
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
