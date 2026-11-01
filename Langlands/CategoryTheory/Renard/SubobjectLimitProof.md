# Renard A.IV: subobject intersections and unions as limits and colimits (proof)

Author: Worker 840.

This pair proves the unchanged published proposition
`Langlands.Renard.SubobjectLimit.SubobjectLimitStatements` from
[`SubobjectLimitStatements`](SubobjectLimitStatements.md), whose statement
author is Worker 709.

Module: `Langlands.CategoryTheory.Renard.SubobjectLimitProof`.
Namespace: `Langlands.Renard.SubobjectLimit`.
The closing theorem is
`Langlands.Renard.SubobjectLimit.subobjectLimitStatements`. It is closed,
has the three independent universe parameters `vC`, `uC` and `uI`, and
has exactly the published aggregate type
`SubobjectLimitStatements.{vC, uC, uI}`. Its conjunction is in
intersection-then-union order. The module imports only the published
statement module, which is unchanged together with everything it imports.

## Source and provenance

The proposition is the derived interpretation, recorded in the statement
pair, of David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
It interprets A.IV.1 example 6 and the union dual in A.IV.2 (printed
p.257 / one-based PDF263). It uses the A.I.2 definitions of intersection
and union as greatest lower and least upper bounds in the factorization
order (printed p.248 / PDF254). On PDF263, which was reread for this
proof, example 6 leaves the interpretation to the reader, and A.IV.2
lists unions of subobjects among the dual colimit examples. Neither
passage gives a proof. The argument below is an internal proof built on
pinned Mathlib's comparison of (co)limits with order bounds in a preorder
category.

## The category on `Subobject X`

Mathlib defines `Subobject X` as `ThinSkeleton (MonoOver X)` and installs
a partial order: `P ≤ Q` exactly when the monomorphism representing `P`
factors through the one representing `Q`. Mathlib installs no separate
category instance on `Subobject X`. Its category is therefore the
canonical one of that order, `Preorder.smallCategory`, in which a
morphism `P ⟶ Q` is a wrapped proof of `P ≤ Q`. The published statement
takes its cones and cocones in exactly this category. Mathlib's preorder
lemmas in `Mathlib.CategoryTheory.Limits.Preorder`, stated for any
preorder, therefore apply to the statement's own diagram
`Discrete.functor F`, cone `t` and vertex `t.pt` without any conversion.

## Reconciling the two ranges

The Mathlib lemmas speak of `Set.range (Discrete.functor F).obj`, a set
indexed by `Discrete I`. The statement speaks of `Set.range F`, indexed by
`I`. The private lemma `range_discrete_functor_obj` proves these sets are
equal for every family `F : I → P` into a category `P`. An object of
`Discrete I` has the form `⟨i⟩` with `i : I`, and
`(Discrete.functor F).obj ⟨i⟩` is `F i` by definition. So each member of
one range is a member of the other. The argument uses no element of `I`;
it holds for empty and infinite index types. Each component proof starts
by rewriting `Set.range F` backwards along this equality.

## Intersections as limits

`intersectionLimitStatement` proves
`IntersectionLimitStatement.{vC, uC, uI}`. After introducing `C`, its
category instance, `X`, `I`, `F` and the supplied cone `t`, and after the
range rewrite, it proves both directions.

- From a witness `ht : IsLimit t`, `Preorder.isGLB_of_isLimit` gives
  `IsGLB (Set.range (Discrete.functor F).obj) t.pt`. Inside that lemma,
  each leg `t.π.app ⟨i⟩ : t.pt ⟶ F i` is read as `t.pt ≤ F i`, so `t.pt` is
  a lower bound. For any lower bound `P`, the lemma forms the cone with
  vertex `P` whose legs are the inequalities `P ≤ F i`. The lift of
  that cone, `ht.lift : P ⟶ t.pt`, is the factor map from the lower-bound
  vertex into the limiting vertex, and it is read as `P ≤ t.pt`. So `t.pt`
  is the greatest lower bound.
- From `h : IsGLB … t.pt`, `Preorder.isLimitOfIsGLB _ t h` builds a
  witness `IsLimit t` for the supplied cone itself, and it is wrapped in
  `Nonempty`. For every competing cone `s`, the legs of `s` show that
  `s.pt` is a lower bound. The greatest-lower-bound property `h.2` then
  gives `s.pt ≤ t.pt`, whose morphism `s.pt ⟶ t.pt` is the lift. The
  factorization and uniqueness equations hold automatically, since
  any two parallel morphisms in an order category are equal.

## Unions as colimits

`unionColimitStatement` proves `UnionColimitStatement.{vC, uC, uI}` for a
supplied cocone `t` in the dual way.

- From `ht : IsColimit t`, `Preorder.isLUB_of_isColimit` gives
  `IsLUB (Set.range (Discrete.functor F).obj) t.pt`. Each leg
  `t.ι.app ⟨i⟩ : F i ⟶ t.pt` is read as `F i ≤ t.pt`, so `t.pt` is an upper
  bound. For any upper bound `P`, the cocone with vertex `P` and legs
  `F i ≤ P` has a descended map `ht.desc : t.pt ⟶ P`. This map goes from the
  colimiting vertex to the upper-bound vertex, and it is read as
  `t.pt ≤ P`. So `t.pt` is the least upper bound.
- From `h : IsLUB … t.pt`, `Preorder.isColimitOfIsLUB _ t h` builds a
  witness `IsColimit t` for the supplied cocone. For every competing
  cocone `s`, its legs make `s.pt` an upper bound. Then `h.2` gives
  `t.pt ≤ s.pt`, whose morphism `t.pt ⟶ s.pt` is the descended map. The
  remaining equations again hold by thinness.

## The aggregate

`subobjectLimitStatements` is the pair
`⟨intersectionLimitStatement.{vC, uC, uI}, unionColimitStatement.{vC, uC, uI}⟩`.
The development check reports the axioms `propext`, `Classical.choice` and
`Quot.sound`, all from Lean's core library. Both component theorems are
public and carry the same three universe parameters. The range lemma is
private.

## Scope

No bound-existence, lattice, smallness, well-poweredness, additive,
abelian, completeness or cocompleteness hypothesis is used, and no
universal witness is assumed. The ambient category `C` is arbitrary. The
index type `I` may be empty, in which case the two comparisons concern a
greatest and a least subobject, or of any cardinality in universe `uI`.

The theorem characterizes when the supplied cones and cocones are
universal. It does not assert that any family has an intersection or a
union. Its colimits are colimits in `Subobject X`, not colimits of
underlying representatives in `C`. The general cone bridge, indexed
subobject image sums and the A.VI.2 existence result, conditional
abelian-category completeness, elementary shapes, ordered systems,
concrete abelian-group examples and filtered colimits are separate units
with their own owners. This proof does not complete A.IV, Appendix A or
the whole-book program.
