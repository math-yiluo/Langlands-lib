# NYLL M026.019: transitivity of relative norms in a finite tower

`Langlands.NYLL.ClassFormation.DegreeData.FiniteTower.norm_trans_apply` proves the
published proposition
`Langlands.NYLL.ClassFormation.DegreeData.FiniteTower.norm_trans_applyStatement`
of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.Statements`.

## Statement

The parameters are, in order, the section variables implicit
`G : IntegralRepGroupType` with instances `[Group G]` and `[TopologicalSpace G]`,
the explicit section variable `T : DegreeData.FiniteTower G`, and explicit
`A : Rep ℤ G` and `a : ambientFixedAddSubgroup A T.top`. The type of the theorem
is exactly `norm_trans_applyStatement T A a`, which unfolds to

```lean
relativeNorm A T.base T.middle T.middle_le_base
    (relativeNorm A T.middle T.top T.top_le_middle a) =
  relativeNorm A T.base T.top (T.top_le_middle.trans T.middle_le_base) a
```

In words: for a finite tower `G_top ≤ G_middle ≤ G_base` of abstract-field
subgroups and an element `a` of the `G_top`-fixed submodule `A_top`, taking the
relative norm from `top` to `middle` and then from `middle` to `base` equals the
relative norm from `top` to `base`. The finiteness instances used by the three
norms are `T`'s two adjacent finite-quotient instances and the published
composite instance `DegreeData.FiniteTower.totalQuotientFinite`.

## Implemented proof

The module contains four declarations. The first two are private local
helpers, the next two are the source-private theorems M026.017 and M026.018,
ported as private theorems, and the last is the target.

1. `relativeNormApplyCoeLocal` (private) states
   `((relativeNorm A K L hLK a : ambientFixedAddSubgroup A K) : A.V) =
   relativeNormValue A K L hLK a` and is proved by `rfl`. It is a local copy of
   the source simp lemma `relativeNorm_apply_coe` (M024.010), whose published
   statement `relativeNorm_apply_coeStatement` has no published proof yet; it
   is private and has a different name, so no second copy of M024.010 is
   published. It holds definitionally because the `toFun` of the published
   `relativeNorm` is `⟨relativeNormValue A K L hLK a, _⟩`.
2. `relativeCosetActionMkLocal` (private) states
   `relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1` and is
   the published proof `relativeCosetAction_mk A K L hLK a k` (M024.002, module
   `...Degree.Norm.U002.Proofs`) read at its unfolded type. The published
   theorem has the opaque type `relativeCosetAction_mkStatement A K L hLK a k`,
   which `rw` cannot use as an equation, so the restatement exposes the
   equation.
3. `relativeCosetAction_towerProductEquiv` (private, M026.017). For
   `M ≤ L ≤ K`, `a : A_M`, `q : K ⧸ G_L` and `r : L ⧸ G_M`, the coset action
   from `M` to `K` at `(Subgroup.quotientTowerEquiv hML hLK).symm (q, r)` equals
   `A.ρ (Quotient.out q).1 (relativeCosetAction A L M hML a r)`. The proof
   inducts on `r` with `Quotient.inductionOn'`; for a representative `x`, the
   inverse tower equivalence sends `(q, ⟦x⟧)` to
   `⟦Quotient.out q * Subgroup.inclusion hLK x⟧` by `rfl`; two rewrites by
   `relativeCosetActionMkLocal` reduce the goal to
   `A.ρ ((Quotient.out q).1 * x.1) a.1 = A.ρ (Quotient.out q).1 (A.ρ x.1 a.1)`,
   which follows from `map_mul` and `rfl`. Here `Subgroup.quotientTowerEquiv`
   resolves to the published `Langlands.NYLL.Subgroup.quotientTowerEquiv`.
4. `finiteTowerNormTransApplyAux` (private, M026.018). For `M ≤ L ≤ K` with
   finite quotients `K ⧸ G_L` and `L ⧸ G_M`, and with the composite finiteness
   instance `relativeTowerQuotientFinite K L M hML hLK` bound by `letI`, it
   proves `relativeNorm A K L hLK (relativeNorm A L M hML a) =
   relativeNorm A K M (hML.trans hLK) a`. After `Subtype.ext`, it fixes
   `Fintype.ofFinite` structures on the two adjacent quotients, introduces the
   `Fintype` structure on `K ⧸ G_M` transported from the product by the
   inverse tower equivalence, and identifies it with `Fintype.ofFinite` by
   `Subsingleton.elim`. It proves that each outer coset term equals
   `A.ρ (Quotient.out q).1 (relativeNormValue A L M hML a)` (by
   `Quotient.out_eq'`, `relativeCosetActionMkLocal` and
   `relativeNormApplyCoeLocal`), unfolds both sides by
   `relativeNormApplyCoeLocal` and `relativeNormValue`, rewrites the outer sum
   termwise, distributes `A.ρ` over the inner sum by `map_sum`, combines the
   double sum into a sum over the product by `Fintype.sum_prod_type`, rewrites
   each product term by M026.017, and reindexes the sum along the inverse tower
   equivalence by `Equiv.sum_comp`.
5. `DegreeData.FiniteTower.norm_trans_apply` (the target) is
   `finiteTowerNormTransApplyAux A T.base T.middle T.top T.top_le_middle
   T.middle_le_base a`. The composite finiteness proof in the auxiliary
   theorem and the instance in the target statement are proofs of the same
   proposition `Finite (T.base.toSubgroup ⧸ ...)`, so they agree by proof
   irrelevance and `exact` closes the goal.

The `letI` in M026.018 binds
`show Finite (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) from
relativeTowerQuotientFinite K L M hML hLK`. The published
`relativeTowerQuotientFinite` has the type
`relativeTowerQuotientFiniteStatement K L M hML hLK`; used without `show`, the
instance argument of `relativeNorm` is not type-correct at the instance
transparency used by `simp` and `rw`, and the `rw [htotalFintype]` step fails.
The `show` only gives the same proof its unfolded type.

Imports: the required statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.Statements`,
the published proof module of `relativeTowerQuotientFinite`
(`...Degree.NormLaws.U014.Proofs`, M026.014) and the published proof module of
`relativeCosetAction_mk` (`...Degree.Norm.U002.Proofs`, M024.002). The other
published declarations used are `relativeNorm`, `relativeNormValue`,
`relativeCosetAction`, `ambientFixedAddSubgroup`, `extensionSubgroup`,
`DegreeData.FiniteTower` and `Langlands.NYLL.Subgroup.quotientTowerEquiv`. The
kernel axioms reported by inspection are `propext`, `Classical.choice` and
`Quot.sound`.

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
| M026.017 | `ClassFormation.relativeCosetAction_towerProductEquiv` (private) | 349–368 | private theorem of the same name |
| M026.018 | `ClassFormation.finiteTowerNormTransApplyAux` (private) | 370–431 | private theorem of the same name |
| M026.019 | `ClassFormation.DegreeData.FiniteTower.norm_trans_apply` | docstring 437–438, statement 439–444, proof 445–446 | the target theorem |

The enclosing source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (18), `open CyclicCohomology` (20), `noncomputable section`
(24), `open scoped BigOperators Pointwise` (26), the section variable line 29
and, for M026.019, `namespace DegreeData.FiniteTower` with
`variable (T : DegreeData.FiniteTower G)` (lines 433–435); the port keeps this
context under the namespace prefix `Langlands.NYLL`.

Modifications, all by Worker 735:

- The namespace is prefixed with `Langlands.NYLL`; the source imports are
  replaced by the three published modules listed above.
- The target's conclusion is written as the published
  `norm_trans_applyStatement T A a`; its unfolded form is the source statement.
  The source proof term of M026.019 is unchanged.
- In M026.017 and M026.018 the source rewrites by the simp lemmas
  `relativeCosetAction_mk` and `relativeNorm_apply_coe` use the private
  restatements `relativeCosetActionMkLocal` and `relativeNormApplyCoeLocal`
  described above; the source's `extensionSubgroup K L hLK` binders are kept
  (it is the published `abbrev` for `L.toSubgroup.subgroupOf K.toSubgroup`).
- In M026.018 the `letI` value is wrapped in `show Finite (...) from`, as
  explained above. All other proof steps of M026.017 and M026.018 are the
  source ones.

This is an abstract coset-sum identity of the NYLL abstract-field model. It
discharges no host class-formation, cup, transfer, Tate or reciprocity target.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim, and
the Lean module docstring records the modifications. The existing Library files
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
