# Eventual properness of supplied arithmetic model morphisms

`AdelicSpreadEventualPropernessStatement` is the conjunction of the
function-field and number-field assertions below, in arbitrary common
universe `u`.

Fix a finite set `S` of actual places and two finite-type schemes `X` and
`Y` over the actual outside-`S` integer ring. For every morphism `f : X ⟶ Y`
over this ring, its actual generic-fiber morphism is proper if and only if
there is a finite set `T` containing `S` for which the actual base change of
`f` to the outside-`T` integer ring is proper. Both maps in the assertion are
the morphisms produced by `Over.pullback` along the displayed literal
integer-subring inclusions. The models and their morphism are supplied and
preserved by base change.

The function-field clause assumes a perfect constant field `k`, a field `F`
with its `k`-algebra structure, the specified compatible `RatFunc k` action
and scalar tower, and `FunctionField k F`. It uses
`AlgebraicCurve.Place k F` and `curvePlaceSIntegers`. It imposes no finiteness
assumption on `k` and no separability assumption on the finite extension of
`RatFunc k`. The number-field clause quantifies over every number field `K`
and its actual finite places, using the original subrings
`(S : Set (FinitePlace K)).integer K`. All finite initial sets, including
empty ones, are allowed.

“Finite type” means `LocallyOfFiniteType` and `QuasiCompact` for both
structure morphisms. Neither the models nor their structure morphisms are
assumed affine or separated. Properness concerns the relative morphism
`f` after the indicated base change, rather than either structure morphism.
Mathlib's `IsProper` is the usual scheme-theoretic property.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp. 5–6, Theorem 3.4(2), the properness
clause, and Remark 3.5; the first paragraph of the proof of Proposition 4.4
on printed p. 11 uses this clause to spread proper morphisms. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This is a derived arithmetic specialization of the general filtered-limit
assertion: the actual integer-ring diagrams have colimit the original
field. Their initial rings are noetherian under the stated arithmetic
hypotheses. Consequently the supplied finite-type models are finitely
presented and quasi-separated, so the source's finite-presentation
hypotheses apply without additional assumptions in the statement. Empty
initial sets are a derived extension of the source's nonempty-set
convention; the same original-ring diagrams and finite-superlevel
argument apply.

This unit states the equivalence. Its proof, existence of a model
morphism for an arbitrary generic-fiber morphism, the intrinsic adelic
properness comparison, compactness, stabilization, and whole-paper
completion remain separate obligations.
