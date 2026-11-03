# Trace and correspondences on supported coefficient complexes

This internal construction prolongs the actual finite-covering trace and
proper-pullback/covering-trace correspondence on induced rational spectra to
the existing supported coefficient complexes. Applying the homology functor
then constructs their actual maps on the homology of those complexes.

## Inputs and conventions

The field, presented strict affinoid algebra, rational spectral action, actual
balanced induced spectra and original transport arrows are those of
`InducedRationalCorrespondence`. Field, group, commutative coefficient ring,
coefficient-module and indexing universes are independent (`u`, `v`, `r`, `w`,
`t`). The coefficient category is the entire `SmoothRep.{r,v,w} R G`, with all
its original intertwiners. The supported representation carrier has universe
`max u v w`. Coefficients have no topology.

The complex is supplied in an arbitrary `ComplexShape` on an arbitrary indexing
type. `supportedComplexFunctor` applies the original compact-support coefficient
functor degreewise; its differential is the coefficient differential applied
pointwise. No resolution or geometric interpretation of the input complex is
assumed.

Every covering and properness hypothesis concerns the original induced spectrum
map. Trace requires genuine `IsCoveringMap` and finite literal fibers, including
empty fibers, and uses the unnormalized sum. Pullback requires genuine properness.
Neither a rational pullback object nor automatic covering/properness for
base-changed arrows is asserted.

## Constructed chain maps

`compactSupportTraceNatTrans_id` and `compactSupportTraceNatTrans_comp` package
the existing objectwise trace identities as coefficient-natural identities.
Trace composition retains the explicit covering hypotheses on both original
maps and their original composite; all three finite-fiber premises are visible.
The previously proved finite-composite-fiber lemma can supply the composite
finiteness premise.

`compactComplexTraceNatTrans` is Mathlib's `NatTrans.mapHomologicalComplex`
applied to the original trace transformation. In degree `i`, its value at `y`
is the sum of `s(x)` over every `x` in the actual fiber above `y`, with values
in the original coefficient representation `C.X i`.

`compactComplexCorrespondenceNatTrans` prolongs the original correspondence
transformation. Its degree `i` formula sums `s(a(x))` over the literal fiber of
the covering leg `b` above `y`. The equality
`compactComplexCorrespondenceNatTrans_eq_pullback_trace` identifies it with
the existing proper pullback chain map followed by the new trace chain map.
For a self-span, `compactComplexCorrespondence_self_apply` proves the
pointwise formula `Nat.card (a.inducedMap ⁻¹' {x}) • s(x)` in each degree;
the cardinality can vary with `x` and is never inverted.

These are natural transformations on all coefficient complexes and all their
chain maps. Their chain-map equations are proved by Mathlib's prolongation
construction from the existing full coefficient naturality; they are not
additional compatibility inputs. Identity and composition follow by applying
the identity/composition laws of prolongation to the proved function-level laws.

`compactComplexTraceNatTrans_baseChange` lifts the original cartesian
pullback/trace identity. Its hypotheses retain proper `a,p`, covering `b,q`,
finite fibers of `b,q` and genuine `IsPullback` of the four actual induced maps
in `Types`. `compactComplexCorrespondenceNatTrans_comp` lifts composition of
the spans `X ← S → Y` and `Y ← T → Z` along a supplied actual cartesian
square with legs `e:W→S`, `f:W→T`. Its hypotheses retain proper `a,l,e`,
covering `b,d,f≫d`, finite fibers of `b,f,d,f≫d`, and the same genuine
underlying-map pullback. Covering of `f` is not required because its trace is
not separately used. Composite properness comes from the existing proper-map
composition construction.

## Maps on genuine homology

`compactHomologyTraceNatTrans` and `compactHomologyCorrespondenceNatTrans`
whisker these chain transformations with Mathlib's
`HomologicalComplex.homologyFunctor` in the existing abelian category of
smooth representations. Thus their components are the actual homology maps
of the constructed chain maps, with the proved smooth full-group action.
They remain natural for every coefficient chain map.

The pullback/trace factorization, identity, cartesian base-change and
cartesian span-composition laws are established by whiskering the corresponding
chain-map equalities. The homology composition law for traces retains the
same geometric hypotheses as its chain version. No pointwise formula for an
arbitrary homology class is assumed.

## Provenance and boundaries

All content is internally derived from the original rational compact-support
functors and their proved trace/correspondence identities, the existing
`InducedRationalCompactComplex` construction, and the pinned Mathlib
`Algebra.Homology.Additive` and homology functor. The implemented proof route
uses prolongation to preserve composition, and functorial whiskering to
preserve the resulting identities. It introduces no external-literature
theorem claim.

This constructs homology of supported functions on a supplied coefficient
complex. No identification with geometric compact-support cohomology, etale
cohomology or a Godement resolution, no higher derived trace, no exactness or
homology-commutation of the coefficient functor, and no arithmetic Hecke or
Harris comparison is claimed. Those remain wider-task obligations.
