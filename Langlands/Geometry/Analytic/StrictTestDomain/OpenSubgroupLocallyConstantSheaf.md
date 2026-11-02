# Full locally constant modules on the finite rational transport site

Author: Worker 13.

This internal construction gives an actual module sheaf on the existing
`OpenSubgroupTransport.finiteTopology`. It uses every object and labelled arrow
of that category and proves matching, gluing and uniqueness for its original
finite covering sieves. The entry declaration is
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.locallyConstantSheafFunctor`.

The base is a complete ultrametric normed field `K` and a presented strict
affinoid algebra `P`. A topological group `G` acts by a
`RationalSpectralAction G P`. An object `X` retains its actual open subgroup,
chosen invariant rational presentation and original rational locus subspace.
Coefficients are an arbitrary algebraic representation `M : Rep R G` over a
commutative ring `R`. The scalar, group, coefficient ring and coefficient carrier
universes `u`, `v`, `r`, `w` are independent. Section modules have carrier universe
`max u w`, even when `v` is larger. Coefficients require no topology.

## Original point maps and finite descent

`Hom.locusMap` is the continuous map on the original locus subspaces associated
to an arrow `f : X ⟶ Y`. Its value is `ρ(f.label) • x`. Continuity follows from
the actual inverse bounded algebra map defining the spectrum action. The
identity and composition formulas are proved by the action laws.

Each rational locus is compact by the published rational representation theorem,
and its ambient spectrum is Hausdorff. For an original finite covering family
`f i : D i ⟶ Y`, `familyCovers_isQuotientMap` proves that the map from the finite
disjoint union of source loci to the target locus is a quotient map. Its
surjectivity is exactly the point-image covering condition. The result applies
also to empty loci and empty covering families.

`isLocallyConstant_iff_of_familyCovers` then says that a function on the target
locus is locally constant precisely when its composites with all these labelled
point maps are locally constant. The reverse implication uses the published
quotient-descent criterion and openness on a disjoint union.

## Full section modules and matching

`locallyConstantPullback M f` is the actual linear map on the entire
`LocallyConstant` modules, with formula

```text
(f* s)(x) = M.ρ(f.label⁻¹)(s(f.locusMap x)).
```

`locallyConstantPresheaf M` has object
`ModuleCat.of R (LocallyConstant X.domain.obj.locus M)` and these pullbacks.
Its identity and composition laws use the inverse-label convention and the
representation laws. `locallyConstantTypePresheaf` explicitly displays the same
functions and maps in `Type (max u w)`. `locallyConstantForgetIso` identifies it
with the module presheaf followed by the ordinary forgetful functor.

For a compatible family `p` on a sieve, `locallyConstantCompatible_apply`
compares values on any two arrows `f : X ⟶ Y` and `g : Z ⟶ Y` whose chosen
points have the same image. It proves

```text
M.ρ(f.label)(p_f(x)) = M.ρ(g.label)(p_g(z)).
```

The proof uses the existing translated rational intersection `refinement f g`
with its common open subgroup and the original arrows `refinementLeft` and
`refinementRight`. Equality of target points places the source point in that
intersection. Evaluating the matching equation there and applying the forward
coefficient operator gives the displayed equality. No pullback universal
property for this refinement is assumed.

## Gluing and the module sheaf

`exists_locallyConstantSieveValue` uses point coverage and the preceding matching
calculation to produce a well-defined target value at each target point:
choose any local preimage and transport its coefficient forward by the arrow
label. `locallyConstantSieveGlueFun` chooses this determined value. Its evaluation
formula holds for every arrow of the covering sieve, including arrows outside
the selected finite covering family. No default coefficient value is used.

`locallyConstantSieveGlue` proves that this function is locally constant. Along
each member of a finite witnessing cover it equals the corresponding local
section postcomposed with a fixed coefficient operator, so the finite quotient
criterion applies. `locallyConstantSieveGlue_isAmalgamation` cancels forward and
inverse coefficient operators to recover every original restriction.
`locallyConstantSieveGlue_unique` tests another amalgamation at covering
preimages and applies the forward coefficient operators. Thus
`locallyConstantTypePresheaf_isSheaf` proves the unique-amalgamation condition
for all covering sieves.

`locallyConstantForget_isSheaf` transfers this result through the identity
forgetful isomorphism. `locallyConstantPresheaf_isSheaf` reflects the required
limits to modules without imposing a bound on the group universe. For any
diagram and cone whose underlying cone is a limit, its underlying section type
is small because that limit already exists. Mathlib's module limit construction
and its preserved underlying limit therefore apply. Reflection of isomorphisms
then reflects the given cone's limit property. This supplies the local
`ReflectsLimitsOfSize` instance used by the sheaf reflection theorem.
`locallyConstantSheaf M` packages the constructed presheaf and proved sheaf
condition as an actual Mathlib module sheaf.

`locallyConstantCoefficientMap a` postcomposes every section value with the
original coefficient intertwiner `a`. Its naturality follows from the
intertwining equation at `f.label⁻¹`; its evaluation formula is proved.
Identity and composition give `locallyConstantSheafFunctor` from ambient
algebraic representations to these full module sheaves.

## Provenance and scope

This is internal derived mathematics from the published
`OpenSubgroupTransportCovering` category and topology, the rational compactness
and representation results, the full `LocallyConstant` module operations,
`LocallyConstant.QuotientDescent`, and pinned Mathlib's sheaf and module-limit
interfaces. It introduces no new original-literature claim. The original
translated refinement, original finite covers and explicit matching calculation
provide the descent proof; sheafness is not supplied as input data.

The construction retains distinct group labels, presentations with equal loci,
trivial scalar valuations, empty loci and all locally constant functions. It
asserts no smoothness of these section representations for arbitrary algebraic
coefficients. Smooth coefficients and continuous local subgroup actions require a
separate smoothness construction. Full analytic or etale sites, structure-sheaf
descent, compact support, derived cohomology, arithmetic coefficients and Harris
specialization remain obligations of the broader task.
