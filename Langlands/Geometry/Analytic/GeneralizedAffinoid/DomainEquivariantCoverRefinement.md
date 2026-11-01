# Equivariant actual spectrum maps of finite cover refinements

Author: Worker 56.

This internal construction lifts the actual refinement category of supplied
finite represented-domain covers to equivariant spectrum diagrams over the
original target locus. It uses the existing finite disjoint-union action,
bounded refinement maps and quotient maps, retaining all their data.

## Inputs and action at a preserving subgroup

Let `K : Type u` be a complete ultrametric normed field, let `P` be an
actual presented positive-polyradius affinoid quotient, and let `G : Type v`
be a topological group. Its universe is independent of the field universe.
Fix `ρ : DomainSpectralAction G P`, an open subgroup `H`, an invariant
represented domain `d : ρ.InvariantDomain H`, a finite cover `c` of
`d.obj`, and a witness
`hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)`.

The witness gives an actual continuous inclusion
`H →ₜ* ρ.finiteFamilyOpenSubgroup H c.obj`, since `H` preserves every
component. `invariantCoverSpectrumAction` restricts the preceding
`finiteCoverSpectrumAction` along this inclusion. Its underlying space is
exactly the original topological disjoint union

```text
Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra.
```

The theorem `invariantCoverSpectrumAction_mk` identifies its operator at
`g : H`: it preserves `i` and applies the existing invariant section-spectrum
action to the second coordinate. That action pulls seminorms back along
the inverse of the constructed forward bounded section automorphism.
Invariance proofs do not change these actual operators.

`invariantCoverQuotient` restricts the preceding equivariant quotient by
the same inclusion. Its underlying map is exactly `TopCat.ofHom c.totalMap`,
as exposed by `invariantCoverQuotient_hom`. The target is the original
represented subspace `d.obj.locus` with its restricted ambient action.
`invariantCoverQuotient_isQuotientMap` reuses the original quotient theorem
for that actual topology.

## Actual refinement maps

Let `b` be another finite cover of the same target, with a witness that
`H` preserves its components, and let
`r : Domain.FiniteCover.Refinement b c`. The construction
`invariantCoverSpectrumMap` has the unchanged continuous map
`TopCat.ofHom r.spectrumMap` as its underlying map. Its application theorem
gives the exact formula

```text
⟨j, x⟩ ↦ ⟨r.index j, (r.map j).spectrumMap x⟩.
```

Here `r.map j` retains the bounded algebra restriction from the chosen
coarser component to the finer component. Its spectrum map is the
actual seminorm pullback along that restriction. The proof of equivariance
uses the commuting equation of this arrow under
`invariantSpectrumActionFunctor H`, then inserts both sides into the
same chosen summand. It does not recover algebra-map equality from
spectrum-map equality.

`invariantCoverSpectrumMap_over_target` proves equality of equivariant
morphisms

```text
invariantCoverSpectrumMap r ≫ invariantCoverQuotient c =
  invariantCoverQuotient b.
```

The underlying equation is the preceding actual refinement spectrum
triangle `r.spectrumMap_over_target`. Individual refinement arrows need
not be surjective, and the index function need not hit every component.

## Refinement diagram and subgroup restriction

`invariantCoverProperty` requires every original cover component to be
`H`-invariant. `InvariantFiniteCover` is its full subcategory in the
existing category of actual finite covers. It retains all chosen index
functions and bounded component arrows. It need not be thin: different
index choices are still different refinement data.

The entry construction `invariantCoverSpectrumOverFunctor` maps this
category to `Over (ρ.invariantLocusAction H d)`. Its object at `c` is
the actual equivariant quotient of its finite spectrum disjoint union.
Its map at a refinement is the constructed equivariant spectrum map,
with the preceding target triangle as its overcategory equation.
The identity and composition laws follow by extensionality: on a
summand, identity retains the index and seminorm, and composition
composes the selected index functions and the actual bounded pullbacks.
The three projection lemmas expose the exact source actions, quotient
morphisms and refinement morphisms of this functor.

For an open subgroup `J ≤ H`, `invariantCoverRestriction` keeps every
cover and refinement while weakening its component invariance witnesses.
`invariantCoverSpectrumAction_subgroup` and
`invariantCoverQuotient_subgroup` identify subgroup restriction with the
corresponding constructions at `J`. These are definitional equalities.
The theorem `invariantCoverSpectrumOverFunctor_subgroup` compares the
complete overcategory diagrams: restricting the covers first agrees
with applying `Over.post` to the ordinary action-restriction functor.
It retains the actual maps as well as the objects and operators.

For arbitrary supplied covers `c` and `b`, their preceding constructed
`commonCoverOpenSubgroup H c b` preserves both original families. The
construction `commonCoverSpectrumMap` applies the fixed-subgroup map
there after restricting `d` to that subgroup. Its underlying map is
again exactly `TopCat.ofHom r.spectrumMap`. Thus every supplied refinement
has this equivariant realization without assuming equality of the two
covers' separate maximal open stabilizers.

## Provenance and limits

This is an internal consequence of `DomainEquivariantCoverDescent`,
`DomainFiniteInvariantCover`, `DomainInvariantActions`,
`DomainCoverRefinement` and subgroup restriction. The new equivariance
proof uses the existing commuting equation for actual bounded domain
arrows. The category laws use their concrete spectrum pullbacks. The
subgroup comparisons retain the original ambient group element and
all underlying maps. No additional literature theorem is claimed.

The imported finite common-stabilizer support adapts Worker 36's
strict rational finite-intersection pattern; that support is included
unchanged when needed for integration.

Empty covers and loci, zero quotients, nilpotents and trivial scalar
valuations remain allowed. The actions in `Action TopCat H` have
continuous fixed-element operators. Joint continuity in the group
parameter, spectrum injectivity, algebra-section descent, analytic
structure sheaves, analytic atlases, analytic etale sites and the
Harris specialization are further obligations.

The subgroup inclusion used here is the published
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.openSubgroupInclusion`,
reused through `DomainInvariantSubgroupRestriction`.
