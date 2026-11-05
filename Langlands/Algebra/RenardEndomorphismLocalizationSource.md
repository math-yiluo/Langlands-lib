# Raised sources and the transported chosen localization arrow

Worker 1581. This is the source-side internal construction for the chosen
endomorphism-localization comparison. All declarations are in
`Langlands.Renard.EndomorphismLocalization.ChosenComparison`.

For every commutative unital ring `R : Type u`, with independent carrier and
enlargement universes `v` and `w`, put κ = max u v w. The construction uses
arbitrary modules, including zero modules, and arbitrary specified endomorphisms.
The zero ring is allowed. No finiteness, injectivity, invertibility, nontriviality
or smallness assumption is added to the source pairs.

`chosenFunctor` is exactly the published composite `toPolynomial R`,
`ModuleLocalization.chosenLocalFunctor (powersX R)` and
`localFromPolynomial R`. Its codomain is the actual full subcategory of
invertible pairs in carrier universe κ. The declarations `chosenFunctor_obj`
and `chosenFunctor_map` expose the original chosen objects and localized
polynomial maps in that composite.

`polynomialRaisedFunctor` is exactly `toPolynomial R`, then the published
`sourceRaisingFunctor` on polynomial modules, then `fromPolynomial R`.
`raisedFunctor` instead sends a pair A to `ModuleCat.of R (ULift.{max u w} A.a)`
with operator `x ↦ ULift.up (A.str x.down)`. Every original intertwiner f is sent
to `x ↦ ULift.up (f.f x.down)`; the definition proves its intertwining, identity
and composition laws.

`sourceLinearEquiv` identifies those two actual source modules. Its forward
function is `ULift.up x ↦ ULift.up (Module.AEval'.of a x)`, where a is A's
specified endomorphism; its inverse uses `(Module.AEval'.of a).symm`.
Its scalar proof explicitly identifies the restricted action of r with the
polynomial action of `C r`, then uses `toPolynomial_C_smul`.
`sourceLinearEquiv_intertwines` uses `toPolynomial_X_smul` to identify the
recovered X-action with the original operator. Thus the comparison includes
the actual AEval carrier and scalar action, beyond an equality of polynomial
object names. `sourceIso` bundles this equivalence as an isomorphism of pairs;
`sourceComparison` is the natural isomorphism beta. Its naturality holds for
every intertwiner by equality of the underlying functions. The two component
formulas and both inverse equations are recorded explicitly.

`polynomialArrow` is theta: the published `chosenLocalizationUnit`, whiskered
on the right by `fromPolynomial R` and on the left by `toPolynomial R`.
The published inclusion-square definitions identify its codomain with
`chosenFunctor R` followed by the inclusion of invertible pairs.
`polynomialArrow_app` identifies the component with `fromPolynomial R` applied
to the actual `canonicalModuleMap`; `polynomialArrow_up` gives its exact
formula `ULift.up m ↦ ULift.up (LocalizedModule.mk m 1)`.
`chosenArrow` is lambda, the composite of beta's forward transformation and
theta. Its formula is
`ULift.up x ↦ ULift.up (LocalizedModule.mk (Module.AEval'.of a x) 1)`.
Naturality is inherited from the two actual natural transformations and also
recorded as `chosenArrow_naturality`. `fieldChosenFunctor` is the exact
arbitrary-field specialization and retains arbitrary vector-space dimension.

The motivating original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
A.III.1, printed251–252 / one-based PDF257–258, defines the right universal
problem and translates module localization in example 4 to endomorphism
localization in example 5 by the polynomial-module equivalence. Worker 1581
reread both pages for this construction. The general commutative-ring form,
ULift choices and explicit natural source comparison are derived internal
content, rather than extra literal assertions of the book. The construction
uses endomorphism invertibility as locality; the printed stronger scalar-inverse
parenthesis in example 4 is not used. See the published
[discrepancy note](../../notes/renard/appendix-a-corrections.md).

This pair constructs the source and transported arrow. The explicit localized
target functor, target comparison and structured-arrow isomorphism are the
next unit of the same task. Initiality, factorization, uniqueness, adjunctions,
chosen-model exactness and the source B-module comparison remain separate
successor obligations. No universal property is asserted here.
