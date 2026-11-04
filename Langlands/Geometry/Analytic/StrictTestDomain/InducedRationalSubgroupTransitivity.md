# Original rational subgroup transitivity

This module constructs the full ordinary equivariant direct-image comparison
for successive subgroup restrictions of a fixed rational domain. It proves
composition of the original arrows, coefficient pullbacks and unnormalized
traces, including the natural transformations on all original coefficients and
the compactly supported smooth coefficient maps.

The namespace is
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport`.

## Original objects and hypotheses

Let `K : Type u` be a complete ultrametric normed field, let `P` be a presented
strict affinoid `K`-algebra, and let `ρ : RationalSpectralAction G P` for a
topological group `G : Type v`. Fix open subgroups `W ≤ V ≤ U`, with inclusion
proofs `k : W ≤ V` and `h : V ≤ U`, and an originally `U`-invariant rational
domain `d`. All restrictions retain its original rational presentation, local
spectrum, topology and restricted action.

Write `X`, `Y` and `Z` for the original transport objects obtained from `d`
at levels `W`, `V` and `U`. Define

```text
f = subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d) : X ⟶ Y
g = subgroupRestriction h d                                       : Y ⟶ Z
q = subgroupRestriction (k.trans h) d                             : X ⟶ Z.
```

The direct and iterated `W` objects are definitionally equal. The original
subgroup arrows have label `1` and keep the underlying rational presentation.
`subgroupRestriction_id` proves that the identity restriction is the identity
arrow. `subgroupRestriction_comp` proves `f ≫ g = q` by transport-arrow
extensionality and `one_mul`. `subgroupRestriction_inducedMap_comp` then proves,
at every original quotient point `z`,

```text
q.inducedMap z = g.inducedMap (f.inducedMap z).
```

These results and the ordinary coefficient pullback require no finite-index
hypothesis.

## Actual full direct-image comparison

For arbitrary `A : Type a` with `Category.{b} A`,
`directImageCompIsoOfEq f g q e A` transports the existing full rational
direct-image composition isomorphism along `e : f ≫ g = q`. Its construction is

```text
eqToIso (congrArg (SheafVariation.directImage A) e.symm)
  ≪≫ SheafVariation.directImageCompIso A f g.
```

`subgroupRestrictionDirectImageCompIso h k d A` specializes this construction
at the three original subgroup arrows. Thus it compares the actual direct
image along `q` with direct image first along `f` and then along `g`, on every
ordinary-open equivariant sheaf and morphism.

Let `R : Type r` be a commutative ring, and let `τ : Representation R G M`
for an arbitrary `R`-module `M : Type w`. The coefficient sheaves take values
in `ModuleCat.{max (max u v) w} R` and retain all locally constant sections.
With `I` the displayed direct-image comparison,
`subgroupRestrictionCoefficientMap_comp` proves

```text
coefficientMap q τ ≫ I.hom.app (LocallyConstantSheaf.sheaf τ)
  = coefficientMap g τ ≫ (directImage g).map (coefficientMap f τ).
```

Its Lean type names the original objects and arrows with `let` bindings and
uses `directImageCompIsoOfEq` explicitly. This is the same construction used
by `subgroupRestrictionDirectImageCompIso`.

## Finite relative quotients and full coefficient traces

For the remaining constructions assume only

```text
Finite (V ⧸ W.toSubgroup.subgroupOf V.toSubgroup)
Finite (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup).
```

`finite_relativeQuotient_trans` derives finiteness of
`U ⧸ W.toSubgroup.subgroupOf U.toSubgroup` using Mathlib's nonzero-index
characterization and `Subgroup.relIndex_ne_zero_trans`. Each subsequent
statement introduces that derived witness with `letI`; long-quotient
finiteness is never an additional hypothesis. The existing original-map
subgroup covering results prove all three covering and finite-fiber
conditions. No covering or literal-fiber witness is requested from the caller.

`properSubgroupRestriction_comp` proves the same composition law in the actual
proper transport category, using faithfulness of its inclusion and
`subgroupRestriction_comp`.

`subgroupRestrictionCoefficientTrace_comp` proves

```text
trace q τ =
  I.hom.app (LocallyConstantSheaf.sheaf τ)
    ≫ (directImage g).map (trace f τ)
    ≫ trace g τ.
```

Here the traces are the existing sums over every point in each entire
original fiber. They are definitionally the maps constructed by
`subgroupRestrictionCoefficientTrace`. The Lean statement uses the generic
`SheafVariation.coefficientTrace` names and explicit finite-fiber `letI`
bindings to keep the types of `X`, `f`, `g` and `q` fixed. It does not choose
representatives, discard any cosets, divide by an index, or add a coefficient
dimension or topology requirement.

`subgroupRestrictionCoefficientTraceNatTrans_comp` proves the composition law
on the entire original `Rep.{w} R G` category:

```text
traceNatTrans q =
  whiskerLeft (coefficientFunctor X R) I.hom
    ≫ whiskerRight (traceNatTrans f) (directImage g)
    ≫ traceNatTrans g.
```

This retains every original coefficient intertwiner. The private congruence
lemmas prove these laws by substituting `q` in the existing generic rational
composition laws. No new geometric comparison is assumed.

## Compactly supported smooth coefficients

Let `M : SmoothRep.{r,v,w} R G` be arbitrary. The objects are the previously
constructed smooth representations of locally constant functions with compact
support on the actual induced rational spectra. No locally constant function
is removed except by the stated compact-support condition.

`subgroupRestrictionCompactSupportPullback_comp` proves

```text
pullback q M = pullback g M ≫ pullback f M.
```

Its proof evaluates at an arbitrary original quotient point and applies the
original continuous-map composition formula.

`subgroupRestrictionCompactSupportTrace_comp` proves

```text
trace q M = trace f M ≫ trace g M.
```

It transports the existing compact trace composition law along the equality
of original rational arrows. Each trace is the unnormalized sum over the full
original fiber.

`subgroupRestrictionCompactSupportPullbackNatTrans_comp` and
`subgroupRestrictionCompactSupportTraceNatTrans_comp` prove these identities
on the full original `SmoothRep.{r,v,w} R G` coefficient functors, by evaluating
their components and using the preceding two laws. All original smooth
coefficient intertwiners are retained.

## Provenance and scope

This is an internal construction and deduction from
`InvariantSubgroupRestriction`, `OpenSubgroupTransport`,
`InducedRationalDirectImage`, `InducedRationalSheafTrace`,
`InducedRationalCoveringTrace`, `InducedRationalSubgroupCovering` and
`InducedRationalSubgroupTrace`, together with Mathlib's relative-index lemmas.
The isomorphism transports the already constructed direct image, and every
composition law is proved from original-arrow equality or actual original-map
composition. No external Harris or Berkovich assertion is introduced.

The scope is subgroup change for a fixed rational presentation and
ordinary-open degree-zero coefficient sheaves, plus the existing compact
locally constant function representations. Composition for smooth sheaf direct
images with their lax comparison is separate. General rational coverings,
analytic or etale realization, Godement and higher derived traces, comparison
with geometric compact-support cohomology, arithmetic Hecke identification,
Shimura specialization and Harris compatibility remain obligations.
