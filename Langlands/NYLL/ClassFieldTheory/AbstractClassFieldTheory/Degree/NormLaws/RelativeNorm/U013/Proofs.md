# NYLL M026.013: invariance of the relative norm under the normal-extension action

`Langlands.NYLL.ClassFormation.relativeNorm_normalExtensionAction` proves the
published proposition
`Langlands.NYLL.ClassFormation.relativeNorm_normalExtensionActionStatement` of
module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.Statements`.

## Statement

The parameters are, in order, the section variables implicit
`G : IntegralRepGroupType` with instances `[Group G]` and `[TopologicalSpace G]`,
explicit `A : Rep ℤ G`, `K L : ClosedSubgroup G`,
`hLK : L.toSubgroup ≤ K.toSubgroup` and
`hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal`, the instance
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`, and explicit
`k : K.toSubgroup` and `a : ambientFixedAddSubgroup A L`. The normality and
finiteness binders are written exactly as in the published statement, through
the `Subgroup.subgroupOf` body of the source's `extensionSubgroup K L hLK`. The
type of the theorem is exactly
`relativeNorm_normalExtensionActionStatement A K L hLK hnormal k a`, which
unfolds to

```lean
relativeNorm A K L hLK (normalExtensionAction A K L hLK hnormal k a) =
  relativeNorm A K L hLK a
```

In words: for a finite Galois abstract extension `L | K` (the subgroup `G_L`,
viewed in `G_K`, is normal and of finite index), the relative norm from `A_L`
to `A_K` is invariant under the action `a ↦ k · a` of `k ∈ G_K` on `A_L`.

## Implemented proof

The module contains four declarations: three private local helpers and the
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
   which `simp` and `rw` cannot use as an equation.
3. `normalExtensionActionCoeLocal` (private) states
   `((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup A L)
   : A.V) = A.ρ k.1 a.1` and is the published proof
   `normalExtensionAction_coe A K L hLK hnormal k a` (M026.012, module
   `...Degree.NormLaws.U012.Proofs`) read at its unfolded type, for the same
   reason.
4. `relativeNorm_normalExtensionAction` (the target). A `show` states the
   unfolded statement and `Subtype.ext` reduces it to an equality in `A.V`. The
   proof fixes `Fintype.ofFinite` on `K ⧸ extensionSubgroup K L hLK` and lets
   `e` be the permutation `Equiv.mulRight (QuotientGroup.mk k)` of that
   quotient; the hypothesis `hnormal`, of class type, is the local `Normal`
   instance that makes the quotient a group. It
   proves that every coset term of the translated element is the coset term of
   `a` at the translated coset: for a representative `x`, `simp only` with
   `relativeCosetActionMkLocal` and `normalExtensionActionCoeLocal` turns the
   left side into `A.ρ x.1 (A.ρ k.1 a.1)`; `e ⟦x⟧ = ⟦x * k⟧` holds by `rfl`, and
   `relativeCosetActionMkLocal` turns the right side into
   `A.ρ (x * k).1 a.1`; after a `change` to
   `A.ρ x.1 (A.ρ k.1 a.1) = A.ρ (x.1 * k.1) a.1`, `map_mul` and `rfl` close the
   goal. It then unfolds both norms by `relativeNormApplyCoeLocal` and
   `relativeNormValue`, rewrites the summands by that equality (`simp_rw`), and
   closes the goal by reindexing the sum along `e` with `Equiv.sum_comp`.

Imports: the required statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.Statements`
and the published proof modules of `normalExtensionAction_coe`
(`...Degree.NormLaws.U012.Proofs`, M026.012) and `relativeCosetAction_mk`
(`...Degree.Norm.U002.Proofs`, M024.002). The statement module's import of
`...Degree.NormLaws.Definitions` brings the published `extensionSubgroup` (an
`abbrev` for `L.toSubgroup.subgroupOf K.toSubgroup` in namespace
`Langlands.NYLL.CyclicCohomology`, opened as in the source). Because it is an
`abbrev`, the statement's normality and finiteness hypotheses on
`L.toSubgroup.subgroupOf K.toSubgroup` serve for the `extensionSubgroup K L hLK`
quotients in the proof. The other published declarations used are
`relativeNorm`, `relativeNormValue`, `relativeCosetAction`,
`normalExtensionAction` and `ambientFixedAddSubgroup`; the Mathlib declarations
used are `Equiv.mulRight`, `Equiv.sum_comp` and `map_mul`. The kernel axioms
reported by inspection are `propext`, `Classical.choice` and `Quot.sound`.

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

| Unit | Source name | Source lines | Port |
| --- | --- | --- | --- |
| M026.013 | `ClassFormation.relativeNorm_normalExtensionAction` | docstring 284–285, statement 286–293, proof 294–313 | the target theorem |

The enclosing source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (18), `open CyclicCohomology` (20), `noncomputable section`
(24), `open scoped BigOperators Pointwise` (26) and the section variable line
29; the port keeps this context under the namespace prefix `Langlands.NYLL`.

Modifications, all by Worker 735:

- The namespace is prefixed with `Langlands.NYLL`; the source imports are
  replaced by the three published modules listed above.
- The conclusion is written as the published
  `relativeNorm_normalExtensionActionStatement A K L hLK hnormal k a`, and the
  proof opens with a `show` of its unfolded form, which is the source
  statement. The normality and finiteness binders are written through the
  `subgroupOf` body, as in the published statement.
- The source uses of the simp lemmas `relativeCosetAction_mk`,
  `normalExtensionAction_coe` and `relativeNorm_apply_coe` use the private
  local lemmas described above. All other proof steps are the source ones.

This is an abstract coset-sum identity of the NYLL abstract-field model. It
discharges no host class-formation, cup, transfer, Tate or reciprocity target.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim, and
the Lean module docstring records the modifications. The existing Library files
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
