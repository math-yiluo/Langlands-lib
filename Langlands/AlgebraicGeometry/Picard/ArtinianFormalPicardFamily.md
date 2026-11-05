# Actual pointed Picard objects from formal families

This is an internal construction from `ArtinianAdicEvaluation`,
`ArtinianChartVersality`, and the actual relative Picard geometry. It evaluates
a supplied formal line-bundle system on the actual Picard relative spaces and
equips the result with a specified residue identification. Its provenance is
the quotient and pullback universal properties and the given formal-system
transition isomorphisms.

## Parameters and actual spaces

All constructions retain an arbitrary universe `u`. The base `k` is a
commutative ring, `K` is a field with a `k`-algebra structure, and `R` is any
commutative `k`-algebra. There is an arbitrary ideal `I` of `R` and an actual
scheme morphism `f : X → Spec k`. An Artinian test `A` has its original
`k`-algebra and surjective augmentation to `K`; it need not have a compatible
`K`-algebra structure.

`totalMap f` is the actual relative projection
`Spec R ×[Spec k] X → Spec R`. The formal system `F` has actual bundles on
the adic spaces of this projection. These adic spaces use the pullback order
fixed in `FormalLineBundleSystem`.

For an actual algebra map `α : R →ₐ[k] A.algebra`, `testSpaceMap` is a
pullback lift from the actual relative space
`Spec A ×[Spec k] X` to the differently ordered ordinary base change used
by `ArtinianAdicEvaluation`. Its two projection equations are proved.
No equality of differently chosen pullbacks is assumed.

At a finite bound `I^(n+1) ≤ ker α`, `finiteMap` composes this lift with
the ordinary finite-stage evaluation map. Its projection is the actual
relative map of `Spec α`; its other coordinate is the finite quotient base
map. `finiteMap_transition` proves compatibility with the actual consecutive
adic transition.

## Evaluation and comparisons

`evaluate` is ordinary pullback of `F.obj n` along `finiteMap`, so its
underlying object is an actual locally free rank-one module sheaf on the
original Picard relative space. `evaluationIso` compares it with the
pullback of the earlier ordinary evaluation by the actual
pullback-composition isomorphism.

`laterIso` pulls back the earlier iteration of the original formal-system
transitions and composes it with the two `evaluationIso` comparisons.
`boundsIso` compares any two valid bounds by passing through their maximum.
These declarations assert actual bundle isomorphisms.

For every actual Artinian arrow `q : A → B`, `bound_postcomp` preserves the
same bound for `q ∘ α`. The abstract ring lemma `quotient_lift_postcomp`
uses the quotient universal property to prove postcomposition of the
factor maps. Spectrum functoriality then gives `baseMap_postcomp`, and
equality on the two pullback coordinates proves `finiteMap_postcomp`.
`postcompIso` uses this equality and ordinary pullback composition to compare
pullback of the evaluation over `A` with evaluation over `B` at that bound.

`algebraizationIso` takes an actual bundle on `Spec R ×[Spec k] X` and a
supplied compatible comparison of its entire restriction system with `F`.
The projection equation for `finiteMap`, pullback composition, and the
specified component of that comparison give an isomorphism from its
ordinary relative pullback along `Spec α` to the evaluation. This is a
bundle comparison conditional on the supplied algebraization.

## Specified residue identification

Fix `ε : R →ₐ[k] K` with `I ≤ ker ε`. `residueBound` proves that stage zero
is a valid bound for the residue test. `residueBundle` is the actual
evaluation at that stage on `Spec K ×[Spec k] X`.

Suppose `A.augmentation ∘ α = ε`. For every valid finite bound,
`residueIso` compares this fixed residue bundle with ordinary pullback of
the evaluation along the original residue inclusion of `A`. It first uses
`boundsIso` over the residue test to pass from stage zero to the chosen
stage. It then uses the inverse of `postcompIso` for the actual augmentation
arrow. That arrow has exactly the prescribed residue inclusion as its
spectrum map.

Given an actual residue bundle `M` and a specified isomorphism
`ρ : M ≅ residueBundle`, `pointed` constructs an object of
`ArtinianTestDeformations.Deformations f M A`. Its underlying bundle is the
evaluation. Its original reduction isomorphism is exactly
`ρ ≪≫ residueIso`, as recorded by `pointed_bundle` and
`pointed_reductionIso`. In particular the supplied `ρ` is retained.
For every such augmentation-compatible `α`, the prerequisite
`ArtinianAdicEvaluation.exists_bound` supplies at least one valid bound.

## Scope

The source algebra needs no locality, noetherianity, or completeness
hypothesis for these constructions. The scheme needs no properness or
projectivity hypothesis, and the residue extension need not be finite.
The module proves the displayed bundle comparisons and the stated formula
for the specified reduction. It does not assert further coherence equations
between these comparisons or compatibility of `algebraizationIso` with
pointed reductions. Formal hull existence, a formally versal family,
algebraization existence, openness, and a smooth scheme atlas remain
separate obligations.
