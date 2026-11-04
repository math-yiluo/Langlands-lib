# Covering maps from subgroup restriction on induced spaces

This module constructs the continuous equivariant map

\[
q:G\times_H X\longrightarrow G\times_J X,\qquad
[g,x]_H\longmapsto[g,x]_J
\]

when \(H\leq J\leq G\) and the original action on \(X\) is a continuous
\(J\)-action. If both subgroups are open in \(G\), it constructs a global
product homeomorphism whose first coordinate is exactly \(q\). This proves
that \(q\) is a covering, identifies its entire literal fiber with the
relative coset space, and gives finite fibers and properness when that
relative coset space is finite.

## Provenance and reused constructions

This is an internal construction from the existing actual balanced quotients
in `InducedSpace`, the coset-copy homeomorphisms in `InducedCharts`, and the
induction-in-stages homeomorphism in `InducedStages`. It does not assert a
translation of a particular passage of Harris or Berkovich.

The covering argument uses Mathlib's `IsEvenlyCovered`,
`IsEvenlyCovered.comp_homeomorph`,
`IsEvenlyCovered.to_isEvenlyCovered_preimage`, and
`IsEvenlyCovered.fiberHomeomorph`. Properness uses
`isProperMap_fst_of_compactSpace`. The numerical index is the existing
`Subgroup.relIndex`. The product chart, its projection equation, and its
application to the original quotient map are constructed here.

## Input data, universes, and actions

The ambient group is `G : Type u`, with `Group G`, `TopologicalSpace G`,
and `IsTopologicalGroup G`. The space `X : Type v` has its original
`TopologicalSpace X`, `MulAction J X`, and `ContinuousSMul J X`.
The group and space universes are independent.

The inclusion is an ordinary explicit proof `hHJ : H ≤ J`. The source
action is exactly

```lean
subgroupRestrictionAction hHJ :=
  MulAction.compHom X (Subgroup.inclusion hHJ)
```

and `SubgroupSource hHJ` is `Space H X` with this action explicitly
selected. Thus the source is the original balanced quotient with the
restricted action. No separate action or action-comparison hypothesis is
input. The restricted action is not registered as a global instance;
computational definitions select it locally.

`continuousSMul_subgroupRestrictionAction` proves continuity of this action
by composition with the continuous subgroup inclusion. Its result type
locally selects the same action. This continuity proof does not require
`IsTopologicalGroup G`.

The covering and product-chart statements require
`hH : IsOpen (H : Set G)` and `hJ : IsOpen (J : Set G)`.
They require no finite index, compactness, local compactness, Hausdorff
condition, or nonemptiness assumption on \(X\).

## The original subgroup map

`subgroupMap hHJ` is a continuous map from `SubgroupSource hHJ` to
`Space J X`. It extends the existing continuous unit \(x\mapsto[1,x]_J\)
across the source balanced quotient. The required subgroup equivariance
of that unit follows from `unit_subgroup_smul`.

`subgroupMap_mk` proves the displayed representative formula. The local
point and the ambient group representative are retained. The existing
balanced-quotient universal property also proves
`subgroupMap_smul`: the map commutes with the full original \(G\)-action.

## Untwisting an induced full-group action

`untwistHomeomorph` is also a reusable construction. For a continuous
action of the entire group \(G\) on \(X\), and an open subgroup \(H\),
it gives

\[
G\times_H X\;\simeq_{\mathrm{Top}}\;X\times(G/H).
\]

Here the \(H\)-action on \(X\) is the restriction of the original full
action. The construction first uses `cosetCopiesHomeomorph` to write the
quotient as the topological coproduct of copies of \(X\).
The private `copiesUntwist` sends the copy coordinate \((c,x)\) to
\((c.\mathrm{out}\cdot x,c)\), with inverse
\((x,c)\mapsto(c,c.\mathrm{out}^{-1}\cdot x)\).
The two inverse laws follow from the original group action laws.
The quotient \(G/H\) is discrete because \(H\) is open. This discreteness
and continuity of each fixed group action prove continuity in both
directions.

`untwistHomeomorph_symm_apply` records the inverse formula on the original
balanced quotient:

\[
(x,c)\longmapsto
[c.\mathrm{out},c.\mathrm{out}^{-1}\cdot x]_H.
\]

The construction uses chosen coset representatives. No equivariance
property of this product homeomorphism is asserted.

## A product chart for the subgroup map

Write \(K=H.\mathrm{subgroupOf}\ J\) and \(D=J/K\).
The subgroup \(K\) carries its subtype topology inside \(J\).
`isOpen_subgroupOf hH` proves it is open by taking the inverse image of
\(H\) under the continuous inclusion \(J\to G\).

`subgroupProductHomeomorph hHJ hH hJ` constructs

\[
E:G\times_H X\;\simeq_{\mathrm{Top}}\;(G\times_J X)\times D.
\]

The implemented composite has the following steps:

1. Apply the inverse of `stagesHomeomorph hHJ` to obtain
   \(G\times_J(J\times_K X)\).
2. Use the open-subgroup coset chart for \(J\leq G\), giving a coproduct
   over \(G/J\) of copies of \(J\times_K X\).
3. Apply `untwistHomeomorph K` separately to each copy, using the original
   full \(J\)-action on \(X\). The private `copiesCongr` builds the
   homeomorphism of these coproducts.
4. Use `Homeomorph.sigmaProdDistrib` to move the constant factor \(D\)
   outside the coproduct, then use the original \(J\)-coset chart on the
   remaining factor.

This is a homeomorphism of the actual quotient topologies. It uses chosen
representatives for both coset spaces; no equivariance of \(E\) is
asserted.

`subgroupMap_product_symm` proves
\(q(E^{-1}(y,c))=y\).
The proof expresses \(y\) in its original \(J\)-coset copy, cancels the
outer chart and product rearrangements, and applies the explicit inverse
untwisting formula. `stagesHomeomorph_mk` flattens the two quotient layers.
Then `subgroupMap_mk` and `mk_balance` reduce the result to cancellation
of the chosen representative's action with its inverse.
Consequently `subgroupProductHomeomorph_fst` proves

\[
\operatorname{pr}_1(E(z))=q(z).
\]

The projection comparison is proved for the original map; it is not an
additional input or a replacement definition of that map.

## Covering, entire fibers, and degree

The private `evenlyCovered_fst` explicitly evenly covers the projection
\(Y\times D\to Y\) over the whole target whenever \(D\) is discrete.
`subgroupMapEvenlyCovered` transports that result through \(E\) and uses
the proved first-coordinate equation. Its index space is the entire
relative quotient \(D\).

`isCoveringMap_subgroupMap` converts these evenly covered neighborhoods
to Mathlib's covering predicate, whose designated index at \(y\) is the
literal original fiber.
`subgroupFiberHomeomorph` uses Mathlib's fiber homeomorphism to construct

\[
D\;\simeq_{\mathrm{Top}}\;q^{-1}(\{y\})
\]

for every \(y:G\times_J X\). The right side is the subtype of all original
source points mapping to \(y\).

Under `[Finite (J ⧸ H.subgroupOf J)]`,
`finite_subgroupMap_fiber` transports finiteness through that equivalence.
`card_subgroupMap_fiber` needs no finiteness premise and proves

\[
\operatorname{Nat.card}(q^{-1}(\{y\}))=H.\mathrm{relIndex}\ J.
\]

It uses `Nat.card_congr` and the definition of the relative index.
For infinite types `Nat.card` has its usual zero convention; the full
fiber homeomorphism, rather than this numerical convention, identifies
the fibers in that case.

## Properness and remaining scope

`isProperMap_subgroupMap` assumes the same finite relative coset space.
A finite topological space is compact. Thus projection from
\((G\times_J X)\times D\) is proper by
`isProperMap_fst_of_compactSpace`. Composing with the constructed
homeomorphism and rewriting its first coordinate proves properness of
the original \(q\). No compactness or separation assumption on \(X\),
or compactness assumption on \(G\), enters this argument.

This module treats subgroup restriction of an existing continuous
intermediate-group action. It does not yet identify this map with a
rational-spectrum transport map, prove a covering result for general
rational restrictions, construct analytic or etale local charts, or
establish arithmetic Hecke or Harris comparisons. Those remain separate
obligations of the broader geometric framework.
