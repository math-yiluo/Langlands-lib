# The inertia block is modules over a noetherian algebra: statement

Module `Langlands.Representation.CuspidalSupport.RationalInertiaBlockNoetherianModulesStatement`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `uF, uV`.
The module contains one **statement**, the `Prop`-valued definition
`RationalInertiaBlockNoetherianModulesStatement`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.4.1 and VI.4.4, printed pp.149–159 / PDF pp.155–165.
The Corollary of VI.4.4 and its proof are on printed p.159 / PDF p.165:

> **Corollaire.** La `ℂ`-algèbre `A` est noethérienne.
>
> *Démonstration.* En effet, `Z` est isomorphe à une algèbre de polynômes de
> Laurent à plusieurs variables, donc noethérienne ([25], 3.6.2). D'autre
> part, `A` est un module de type fini sur `Z`. On conclut grâce à ([25],
> 3.6.1). La catégorie `M(G)[π]` est donc équivalente à la catégorie des
> modules à droite sur une algèbre noethérienne.

Here `A = R = End_G(Π)` for the compact induction `Π = ind_{⁰G}^G(ρ)` of an
irreducible summand `ρ` of the restriction of the irreducible supercuspidal
`π` to `⁰G` (VI.4.1). The statement is the last sentence of the proof. The
Corollary itself is the published `RationalSummandEndNoetherianStatement`,
whose Markdown records: "The concluding remark that `M(G)[π]` is equivalent
to modules over a noetherian algebra is not stated."

The provenance is source: the closing assertion of the proof of the
Corollary of VI.4.4.

## Published objects

All objects are published; this file constructs nothing. The binders are
copied from the published VI.4.1 Theorem `RationalSummandHomEquivalenceStatement`
and VI.4.4 Corollary `RationalSummandEndNoetherianStatement`:

- a nonarchimedean local field `F`, a connected reductive `G`
  (`IsConnectedReductive G`), a maximal split torus `i : T → G`, the canonical
  topology on `G(F)` with local compactness, the nonarchimedean group
  property and the Hausdorff property, a generic cocharacter `ν`, the
  standard-cocharacter statement `hStandard`, the relative root system
  `hRoots`, and closedness `hU` of the standard unipotent subgroups. These
  are hypotheses of the published statements, kept here in the same form;
- an irreducible smooth `π` (carrier in `Type uV`) that is cuspidal in the
  published sense `IsCuspidal` for the standard parabolic subgroups;
- the actual inertia block `RationalInertiaBlock G (rationalInertiaBaseLift G π)`
  (Renard's `M(G)[π]`): the full subcategory of smooth representations with
  carriers in `Type (max uF uV)` whose irreducible subquotients are unramified
  twists of `π`; `rationalInertiaBaseLift` lifts `π` to that universe;
- Mathlib's `ModuleCat Rᵐᵒᵖ`, unital right `R`-modules, and
  `IsNoetherianRing R` (left noetherian) and `IsNoetherianRing Rᵐᵒᵖ` (right
  noetherian).

## The statement

`RationalInertiaBlockNoetherianModulesStatement`: for all such data and every
irreducible cuspidal `π`, there are a `ℂ`-algebra `R` with carrier in
`Type (max uF uV)`, left and right noetherian, and an equivalence of
categories between `M(G)[π]` and `ModuleCat.{max uF uV} Rᵐᵒᵖ`.

The summand `ρ` is not part of the statement: Renard's sentence asserts the
existence of such an algebra. The algebra and the module category use the
carrier universe of the block, so that the equivalence is between categories
of objects of the same size.

## Why the statement is true

Choose an irreducible `ρ` of `⁰G` with an injective `⁰G`-map into the
restriction of `π` (the restriction is a direct sum of irreducible
representations, Proposition VI.3.2, as recalled at the start of VI.4.1), and
take `R = End(Π)`. The published VI.4.1 Theorem gives the
equivalence `Hom(Π, ·) : M(G)[π] ≃ ModuleCat (End Π)ᵐᵒᵖ`, and the published
VI.4.4 Corollary gives that `End Π` is left and right noetherian.

## Remaining obligations

The proof is a separate obligation. It needs the published
`RationalSummandHomEquivalenceStatement` and
`RationalSummandEndNoetherianStatement` (check the Library for their
proofs) and the existence of an irreducible summand `ρ`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceStatement` | the binders and objects of VI.4.1: `RationalInertiaBlock`, `rationalInertiaBaseLift`, `IsCuspidal`, `rationalPoint_isTopologicalGroup`, `StandardCocharacterStatement`, `HasRelativeRootSystem`, `isSemidirectDecomposition_of_standardCocharacterStatement` |
| `Langlands.Representation.CuspidalSupport.RationalSummandEndNoetherianStatement` | the companion VI.4.4 Corollary (for the reader; its objects are the same) |
