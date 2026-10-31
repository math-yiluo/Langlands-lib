# Finite stable generation for the original nonunital action: proof

This module proves the published aggregate
`Langlands.Algebra.IntegerOriginalSubmoduleGeneration.IntegerOriginalSubmoduleGenerationStatement`
in the theorem `integerOriginalSubmoduleGeneration`, whose complete type is
`IntegerOriginalSubmoduleGenerationStatement.{uA, uM}` with the independent
universe parameters `uA, uM` in that order. It imports the statement module
`Langlands.Algebra.IntegerOriginalSubmoduleGenerationStatements` by its Lean
name and leaves that module, its Markdown and its imports unchanged. The
aggregate is the ordered conjunction of the submodule, whole-module and
Noetherian comparisons; the closed theorems `submoduleGeneration`,
`moduleGeneration` and `noetherianGeneration` prove them, and
`integerOriginalSubmoduleGeneration` pairs them in that order.

## Setting

The helper section binds an arbitrary possibly noncommutative
`NonUnitalRing A`, an `AddCommGroup M` and the original `NonUnitalModule A M`.
Each helper theorem states its left side with the same `letI` selection of
`CompatibleUnitization.module (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))`
over `Unitization ℤ A` as the target, and its proof installs that same module
with a local `let`; the closed component theorems are these helpers with the
binders of the target supplied. No other action,
module, subgroup structure or global instance is introduced. The only
bridge used is the published order isomorphism
`NonUnitalSubmodule.intUnitizedOrderIso` from the original stable additive
subgroups `NonUnitalSubmodule A M` to the submodules of that selected module.
Since its forward and inverse maps keep the same carrier, membership and
subset statements pass through it definitionally, and its order-reflection
`OrderIso.le_iff_le` turns submodule inclusion into inclusion of original
subgroups.

## The submodule comparison

`fg_intUnitizedOrderIso_iff P` is the first component for one `P`. In the
forward direction, finite generation gives a `Finset` `S` whose ordinary
`Submodule.span` over `Unitization ℤ A` equals the image of `P`. Then
`Submodule.subset_span`, rewritten by that equality, shows `S ⊆ P`. For a
stable subgroup `Q` containing `S`, the inclusion `P ≤ Q` is reduced by
`le_iff_le` to the inclusion of the images, the image of `P` is replaced by
the span, and `Submodule.span_le` reduces this to `S ⊆ Q`.

In the reverse direction, given `S ⊆ P` with the minimality property, the
span of `S` is contained in the image of `P` by `Submodule.span_le`. For the
other inclusion, the minimality property is applied to the original stable
subgroup `intUnitizedOrderIso.symm (span S)`, which contains `S` by
`Submodule.subset_span`. The resulting inclusion is transported back by
`le_iff_le` and `OrderIso.apply_symm_apply`, so the image of `P` equals the
span of `S`, which is the definition of `.FG`.

## The whole-module comparison

`finite_iff_original_stable_generators` rewrites `Module.Finite` by
`Module.finite_def` to finite generation of the top submodule, writes that
top submodule as the image of `intUnitizedOrderIso.symm ⊤`, and applies the
submodule comparison to it. Membership in that subgroup is membership in the
top submodule, which `Submodule.mem_top` supplies for every element; this
also gives the containment of any `Finset` in it. For a stable subgroup `P`
containing `S`, the inclusion `intUnitizedOrderIso.symm ⊤ ≤ P` from the
comparison therefore gives `∀ m : M, m ∈ P`, and conversely
`∀ m : M, m ∈ P` gives that inclusion. The generating `Finset` is the same
on both sides; no top element of the original subgroup type is used.

## The Noetherian comparison

`noetherian_iff_original_stable_generators`: if the selected module is
Noetherian, `IsNoetherian.noetherian` makes the image of every `P` finitely
generated and the submodule comparison yields its finite stable generators.
Conversely, an arbitrary submodule `N` of the selected module is rewritten
as the image of `intUnitizedOrderIso.symm N` by `OrderIso.apply_symm_apply`,
and the hypothesis for that original stable subgroup together with the
submodule comparison makes it finitely generated; this is the
`IsNoetherian` constructor. The finite set may depend on the subgroup.

## Scope

No finiteness, Noetherian, unit-law, nondegeneracy, nontriviality,
commutativity, field or complex hypothesis is added: the helper theorems have
exactly the binders listed above. Empty generating sets, zero actions and the
zero carrier are covered by the same arguments. The Lean uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

This is internal derived algebra. As recorded in the statement's Markdown,
it is motivated by David Renard,
*Représentations des groupes réductifs p-adiques* (French version dated
9 July 2026), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`: the
conventions on printed pp. 5–6 / PDF 11–12, I.2.1 on printed p. 14 / PDF
20–21, A.I.2–A.I.3 on printed pp. 248–249 / PDF 254–255 and C.II on printed
p. 279 / PDF 285. The book does not state these integer comparisons, and the
proof follows no literature route. It makes no claim about categorical
subobjects, the book's complex unitization, its categorical finite-type or
Noetherian predicates, its convention for a possibly nonunital Noetherian
algebra, or the full C.II proposition, which keep their existing owners.

Worker 1101 wrote this proof independently along the route recorded in the
task context; no private draft of another worker was reused.
