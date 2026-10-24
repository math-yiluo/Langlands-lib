# Degree-one vanishing from prime-index normal sections: proof

Authors: Worker 58 (original draft of the three pointwise theorems) and
Worker 263 (closed wrapper, adaptation to the published Sylow proof and this
description).

This module proves the closed proposition of
`Langlands.Cohomology.PrimeSectionH1Statement`:

- `Langlands.Cohomology.primeSectionH1Vanishing :
  Langlands.Cohomology.PrimeSectionH1Vanishing.{u}`.

The proposition quantifies, in this order, `k : Type u` with `[CommRing k]`,
`G : Type u` with `[Group G]` and `[Finite G]`, `A : Rep.{u} k G`, and the
hypothesis that `groupCohomology ((Rep.res H.subtype A).quotientToInvariants N) 1`
is a subsingleton for every `H : Subgroup G` and every `N : Subgroup H` with
`[N.Normal]` and `N.index.Prime`. The conclusion is
`Subsingleton (groupCohomology A 1)`.

All objects are Mathlib's actual ones: ordinary group cohomology
`groupCohomology`, restriction `Rep.res` along subgroup inclusions, and
`Rep.quotientToInvariants`. There is no finiteness hypothesis on `k`, on `A`
or on any cohomology module, and the universe `u` is arbitrary. The module
imports the statement module, the published Sylow proof module
`Langlands.Cohomology.SylowDetectionProof`, and
`Mathlib.GroupTheory.Nilpotent`. It sets no options. Only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` are used.

## Pointwise theorems

The section `Pointwise` fixes `k G : Type u` with `[CommRing k] [Group G]`.
Below, "`M` vanishes" means that the module `M` is a subsingleton.

### Inflation–restriction step

`h1_subsingleton_of_normal A N hN hQ` takes a normal subgroup `N` of `G`. If
`groupCohomology (Rep.res N.subtype A) 1` vanishes (`hN`) and
`groupCohomology (A.quotientToInvariants N) 1` vanishes (`hQ`), then
`groupCohomology A 1` vanishes.

The proof uses Mathlib's `groupCohomology.H1InfRes_exact A N`. It states that
the short complex

`H¹(G ⧸ N, A^N) → H¹(G, A) → H¹(N, A)`,

with inflation as first map and restriction as second map, is exact. A
subsingleton module is a zero object of `ModuleCat k`
(`ModuleCat.isZero_of_subsingleton`). So the first map, whose source is zero,
is the zero map, and the second map, whose target is zero, is the zero map.
`ShortComplex.Exact.isZero_X₂` then shows that the middle term `H¹(G, A)` is a
zero object. `ModuleCat.subsingleton_of_isZero` turns this back into a
subsingleton statement.

### Nested restriction

`h1_subsingleton_nested A H N h` takes a subgroup `H` of `G` and any subgroup
`N` of `H`; no normality is needed. Let `N.map H.subtype` be the image of `N`
in `G`, a subgroup of `G`. If
`groupCohomology (Rep.res (N.map H.subtype).subtype A) 1` vanishes, then
`groupCohomology (Rep.res N.subtype (Rep.res H.subtype A)) 1` vanishes.

The proof takes the group isomorphism
`N.equivMapOfInjective H.subtype H.subtype_injective` from `N` onto its image.
Both representations have the underlying module of `A`, and both act through
`A` on the same element of `G`. So the identity linear equivalence of that
module is compatible with the two actions, and the compatibility holds by
`rfl`. Mathlib's `groupCohomology.mapIso` turns this data into an isomorphism
from the degree-one cohomology of the nested restriction to that of the image
subgroup. Its underlying linear equivalence is injective, so its source
vanishes because its target does.

### Main pointwise theorem

`primeSectionH1Vanishing_of_sections A h` additionally assumes `[Finite G]`.
Its hypothesis `h` is exactly the premise of the closed proposition, and its
conclusion is that `groupCohomology A 1` vanishes.

The proof first establishes an inner claim `hpSub`. For every natural number
`p` with `[Fact p.Prime]` and every subgroup `H` of `G` with `IsPGroup p H`,
the module `groupCohomology (Rep.res H.subtype A) 1` vanishes. The proof is by
strong induction on `m = Nat.card H`, generalizing over `H`. By
`IsPGroup.card_eq_or_dvd`, either `Nat.card H = 1` or `p` divides
`Nat.card H`.

- If `Nat.card H = 1`, then `H` is a subsingleton group
  (`Nat.card_eq_one_iff_unique`). Mathlib's
  `isZero_groupCohomology_succ_of_subsingleton` in degree `0 + 1` shows that
  the cohomology is zero.
- Otherwise `H` is a finite `p`-group, hence nilpotent
  (`IsPGroup.isNilpotent`). `Group.IsNilpotent.exists_normal_index_eq_of_dvd_card`
  gives a normal subgroup `N` of `H` with `N.index = p`. Its image
  `N.map H.subtype` in `G` has cardinality `Nat.card N`
  (`Subgroup.card_map_of_injective`). Since `Nat.card N * p = Nat.card H`
  (`Subgroup.card_mul_index`), `Nat.card N` is positive and `p > 1`, this
  image is strictly smaller than `H`. It is again a `p`-group, by
  `IsPGroup.to_subgroup` and transport along `N.equivMapOfInjective`. The
  induction hypothesis therefore makes its cohomology vanish. The nested
  restriction step transfers this to `N` with coefficients
  `Rep.res N.subtype (Rep.res H.subtype A)`. The premise `h H N`, applied to
  the primality of `N.index = p`, makes the quotient term
  `groupCohomology ((Rep.res H.subtype A).quotientToInvariants N) 1` vanish.
  The inflation–restriction step, applied to the representation
  `Rep.res H.subtype A` of `H` and its normal subgroup `N`, concludes.

Finally the proof applies the published closed theorem
`Langlands.Cohomology.sylowSubsingleton` at `k`, `G`, `A`, degree `1` and
`Nat.one_pos`. This reduces the goal to: for every prime `p` and every
`P : Sylow p G`, the module `groupCohomology (Rep.res P.1.subtype A) 1`
vanishes. That is `hpSub` for the subgroup `P.1`, which is a `p`-group by
`Sylow.isPGroup'`.

## Closed theorem

`primeSectionH1Vanishing` introduces `k`, its ring instance, `G`, its group
and finiteness instances, `A` and the premise, in the statement's order. It
then applies `primeSectionH1Vanishing_of_sections`. The theorem is unapplied,
and its type is exactly the published constant
`Langlands.Cohomology.PrimeSectionH1Vanishing.{u}`.

## Provenance

This is a derived proof of a derived statement. The statement isolates the
group-theoretic content of Emil Artin and John Tate, *Class Field Theory*, AMS
Chelsea, 2009, Chapter XIV, section 2, Lemma 1 and the Remark following it,
printed pp. 147–148 (PDF pp. 156–157). The registered source is
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`. The Remark
takes `r = 1`, `ν = 0` in Lemma 1. Since inflation–restriction is always exact
in degree one, Axiom I′ (`H¹` vanishes on cyclic layers of prime degree)
implies Axiom I (`H¹` vanishes on all normal layers).

The source proof inducts on the degree of a layer. Case 1, a prime-power
degree, uses some proper nontrivial normal subgroup and the
inflation–restriction sequence. Both resulting layers are then handled by
induction. Case 2 uses injectivity of restriction to Sylow subgroups on
primary parts.

The Lean proof follows the same two ingredients in a different arrangement.
It applies Sylow detection once, to `G` itself, through the published
`sylowSubsingleton`. It runs the induction only over `p`-subgroups of `G`.
Within a `p`-group it chooses a normal subgroup of index exactly `p`, which
exists because finite `p`-groups are nilpotent. The quotient term is then a
prime-index section and is covered directly by the premise. Only the subgroup
term needs the induction hypothesis. Working with subgroups of `G` and their
images in `G` keeps every section within the range of the premise.

This module proves no arithmetic statement. It does not show that any
formation satisfies Axiom I′. It also does not compare fixed-field coefficient
modules with invariant submodules. The proof does not assume that restriction
to subgroups of prime order detects `H¹`.
