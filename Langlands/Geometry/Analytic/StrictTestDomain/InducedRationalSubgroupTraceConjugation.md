# Conjugation of original finite-fiber compact traces

This internal construction equips the existing covariant compact trace tower
with conjugation isomorphisms on its full original coefficient category.
The entry definition is
`OpenSubgroupTransport.FiniteIndexLevel.compactTraceTowerConjugationIso`
in the namespace
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction`.
It also constructs the contravariant pullback and whole-group invariant
isomorphisms, proves compatibility with original intersection-span operators,
and identifies the pullback isomorphisms with the compact-function maps used
by the existing Godement tower.

## Inputs and conventions

Fix a complete ultrametric normed field `K`, a presented strict affinoid
algebra `P`, a topological group `G` with `IsTopologicalGroup G`, an actual
`RationalSpectralAction G P`, an open subgroup `U`, an original
`U`-invariant rational presentation `d`, and `g : G`. The coefficient ring
`R` is any commutative ring. These inputs and coefficient modules share an
arbitrary universe `u`.

Every coefficient construction retains the entire
`SmoothRep.{u,u,u} R G` and all its intertwiners. Every original level in
`FiniteIndexLevel U` is retained: an open subgroup below `U` of nonzero
relative index in `U`. No normality, finite-dimensionality, admissibility,
invertibility of an index, or coefficient-topology premise is imposed.

Write `dᵍ` for
`(ρ.invariantConjugationEquivalence U g).functor.obj d`, and `E` for
`conjugationEquivalence U g`. These are explanatory abbreviations.
The moved level `E.functor.obj V` is the actual subgroup `g V g⁻¹`.
For an original arrow `f : V ⟶ W`, write `p_f` for the original
`(rationalArrow d f).inducedMap` and `p_fᵍ` for its moved counterpart.
Let `e_V = inducedConjugationHomeomorph d g V`.

The spectra are the original balanced quotient spaces with their quotient
topology and continuous action of all `G`. All fiber, compact-function,
trace, and invariant constructions before `StableComparison` require no
local stable-neighbourhood premise.

## Literal fibers and the unnormalized sum

`conjugationFiberEquiv d g f y` is an equivalence

```text
{x | p_f x = y} ≃ {x' | p_fᵍ x' = e_W y}.
```

Its forward map sends the original fiber point `x` to `e_V x`, as recorded
by `conjugationFiberEquiv_apply`. The inverse sends `x'` to `e_V.symm x'`.
The existing geometric square
`e_W (p_f x) = p_fᵍ (e_V x)` proves forward fiber membership.
For inverse membership, apply injectivity of `e_W`, use the same square,
and cancel the homeomorphism and its inverse. The two inverse laws are
the original homeomorphism inverse laws on the underlying subtype values.
The finite-fiber instances at both levels are derived from
`finite_rationalArrow_fiber`, so they are not additional assumptions.

For any additive commutative group `A : Type u` and any function `s` on the
moved `V` spectrum, `fiberSum_conjugation` proves

```text
fiberSum p_f (s ∘ e_V) y = fiberSum p_fᵍ s (e_W y).
```

The proof applies `Fintype.sum_equiv` to this literal fiber equivalence.
Both sides sum over the entire original finite fiber. There is no choice
of representatives, division by a degree, or normalization of the trace.

## Full coefficient isomorphisms

`compactConjugationIso d g R V` goes from the moved compact-section
coefficient functor at `E(V)` to the original one at `V`. Its hom is the
existing `Hom.compactSupportPullbackNatTrans` for the original
`rationalConjugationIso d g V` hom, and its inverse is the existing proper
pullback for that same rational isomorphism's inverse. Properness of both
maps was derived from `e_V` in the geometric conjugation construction.
The two inverse identities are proved by evaluation at every coefficient,
compact function, and point, using the actual homeomorphism inverse laws.
Coefficient naturality, linearity and equivariance are inherited from the
original proper pullbacks.

`compactConjugationIso_trace_naturality` proves, for every original arrow,

```text
trace(E(f)) ≫ pullback(e_W) = pullback(e_V) ≫ trace(f).
```

Evaluation reduces this equality of full coefficient natural
transformations to `fiberSum_conjugation`.
`compactTraceTowerConjugationIso` assembles these same components into

```text
E.functor ⋙ compactTraceTower dᵍ R ≅ compactTraceTower d R.
```

`compactConjugationIso_pullback_naturality` proves the contravariant square
by evaluating the original geometric square inside each compact function.
It assembles into

```text
compactPullbackTowerConjugationIso :
  E.functor.op ⋙ compactPullbackTower dᵍ R ≅ compactPullbackTower d R.
```

The `hom_app` and `inv_app` theorems identify the trace components with the
original forward and inverse proper pullbacks. The theorem
`compactPullbackTowerConjugationIso_app` identifies its level isomorphisms
with exactly those of the trace tower.

`compactTraceTowerConjugationIso_apply` evaluates the hom at `s` and `z`
as `s(e_V z)`. Its inverse evaluation is `s(e_V.symm z)`.
The representative theorem `compactTraceTowerConjugationIso_apply_mk`
uses the existing quotient formula

```text
[a,x] ↦ [a * g⁻¹, (rationalConjugationIso d g V).hom.localSpectrumMap x].
```

Thus the inverse group-label correction is retained, and the original
coefficient value is unchanged.

## Whole-group invariants

`invariantCompactTraceTowerConjugationIso` and
`invariantCompactPullbackTowerConjugationIso` right-whisker these actual
isomorphisms by the functor that postcomposes each coefficient functor
with `smoothInvariants R G`. Their targets are coefficient functors into
`ModuleCat R`, with invariants under the entire original group `G`.
Their forward and inverse component theorems identify the maps as
`Functor.whiskerRight` of the original compact components.
The pullback and trace components again agree exactly.

`invariantCompactTraceTowerConjugationIso_apply` evaluates the forward map
on the underlying invariant compact function as `s(e_V z)`. Neither an
exactness hypothesis nor preservation of homology by invariants is used.

## Original intersection-span operators

`compactConjugationIso_span` treats any original span
`V ← A → W`, with arrows `a` and `b`. It proves

```text
pullback(E(a)) ≫ trace(E(b)) ≫ pullback(e_W)
  = pullback(e_V) ≫ pullback(a) ≫ trace(b).
```

The implemented proof evaluates at every coefficient, compact function and
point. It reindexes the whole right-leg fiber by `fiberSum_conjugation`,
then uses the original left-leg geometric square on the summand function.
This retains both original maps and every summand.

`commonRefinementCorrespondence_conjugation` specializes this identity to
the existing canonical span with apex `commonRefinement V W`, the actual
subgroup intersection. In the original inverse-conjugation comap model,
conjugating this intersection is definitionally the moved intersection,
with proof fields irrelevant. This is the same intersection law recorded
by `conjugationOrderIso_commonRefinement`; hence the specialized span is
the original `commonRefinementCorrespondence` on both towers.
`invariantCommonRefinementCorrespondence_conjugation` obtains the identical
square on whole-group invariant coefficient functors by right-whiskering
this equality with `smoothInvariants R G`.

## Agreement with the Godement compact-function tower

Only the final `StableComparison` section assumes the existing original
largest-level local `HasStableNeighbourhoods` premise. The conjugate local
instance is derived by `hasStableNeighbourhoods_conjugate_local`, with no
second local stability assumption.

`compactPullbackTowerConjugationIso_eq_compactFunctions` identifies the
entire pullback isomorphism with the existing
`compactFunctionsTowerConjugationIso`.
`invariantCompactPullbackTowerConjugationIso_eq_compactFunctions` proves
the analogous whole-group invariant equality. Isomorphism and natural
transformation extensionality reduce both proofs to definitional equality
of the original proper pullback components. Thus the trace tower uses
exactly the compact-function conjugation maps that occur in the existing
Godement and degree-zero comparison squares.

## Provenance and remaining obligations

This is an internal construction from
`InducedRationalSubgroupTraceTower`,
`InducedRationalSubgroupConjugation`, and
`InducedRationalSubgroupCohomologyConjugation`. The fiber equivalence and
finite-sum argument derive trace naturality from their original geometric
maps. Natural-isomorphism assembly and whole-group invariants then retain
those same maps. No external literature statement or desired comparison
theorem is supplied as input.

This unit constructs compact-function traces and their conjugation.
It does not construct positive-degree cohomological trace maps, prove
Godement acyclicity or positive-degree sheaf-derived comparison, or
establish invariants-edge invertibility in positive degrees. General
rational coverings, analytic and etale realizations, arithmetic Hecke
identification and convolution, uniformization, Shimura specialization,
and the required Harris compatibility remain separate construction or
theorem obligations of the broader task.
