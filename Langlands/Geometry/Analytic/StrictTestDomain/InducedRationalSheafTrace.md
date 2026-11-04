# Full coefficient sheaf trace on actual induced rational spectra

This module constructs the unnormalized finite-covering trace on full
ordinary-open equivariant coefficient sheaves along the existing actual rational
transport maps. It retains every original coefficient representation and
intertwiner and proves fiber evaluation, pointwise degree, identity and
composition laws with the existing rational direct-image comparisons.

The namespace is
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.SheafVariation`.

## Provenance and inputs

This is an internal specialization of
`Langlands.Sheaf.Equivariant.DirectImage.coefficientTrace` to the maps in
`InducedRationalSpectrum`, using the full sheaf and coefficient functors in
`InducedRationalDirectImage`. It reuses the actual finite-fiber and identity
covering constructions from `InducedRationalCoveringTrace`. No new assertion
from external literature is claimed. The generic sheaf trace already derives
local constancy from genuine covering charts and restriction naturality from
original-fiber equivalences; those obligations are preserved here.

Let `K : Type u` be a complete normed ultrametric field, `P` a presented strict
affinoid algebra over it, `G : Type v` a topological group, and
`ρ : RationalSpectralAction G P`. The objects `X`, `Y`, `Z` of
`ρ.OpenSubgroupTransport` contain the existing open subgroups and invariant
rational quotients. Their local spectra are the actual Banach spectra of those
quotients. Their induced spectra are the actual balanced quotients
`G ×_H X.LocalSpectrum`, in universe `max u v`, with the previously constructed
continuous full-group action.

The commutative coefficient ring `R : Type r` and module `M : Type w` have
independent universes. Coefficients range over all of `Rep.{w} R G`, with all
original linear intertwiners; there is no coefficient topology, dimension or
smoothness premise. Section modules lie in `ModuleCat.{max (max u v) w} R`.
No equality between `u`, `v`, `r`, and `w` is required.

For a rational morphism `f : X ⟶ Y`, its original induced continuous map is

```text
f.inducedMap [a,x] = [a * f.label⁻¹, f.localSpectrumMap x].
```

The local map is the existing spectrum pullback of the bounded rational
restriction. The trace assumes `IsCoveringMap f.inducedMap` and finiteness of
every literal fiber `f.inducedMap ⁻¹' {y}`. These are predicates on this actual
map, rather than replacement spaces or independently supplied trace operators.
This module does not prove them for arbitrary rational morphisms. Mathlib's
covering predicate permits empty fibers; their sums are zero. No properness,
compact-support, subgroup-normality or separation assumption is added.

## Trace on every original open

Write `LC_X(M)` for the existing full locally constant equivariant sheaf.
`coefficientTrace f hf τ` has direction

```text
(directImage f).obj LC_X(M) ⟶ LC_Y(M).
```

It is exactly the generic full sheaf trace for `f.inducedMap`, its proved
full-group equivariance and the given covering proof. Both direct image and
coefficient sheaves retain every ordinary open and labelled restriction.
At an arbitrary target open `U`, its source consists of all locally constant
sections on the actual inverse open `f⁻¹(U)`.

`coefficientTrace_apply` identifies evaluation with `fiberSum` for the actual
restricted point map. `coefficientTrace_apply_sum` reindexes that sum over the
entire original fiber:

```text
(trace_f s)(y) = ∑ x : f.inducedMap⁻¹{y}, s(x).
```

Each point is viewed in `f⁻¹(U)` using its original fiber equation and the
membership of `y` in `U`. A `Fintype` on the fiber is used only to express the
finite sum and is available from the finiteness premise.

`coefficientTrace_pullback_apply` proves the pointwise equation

```text
(trace_f (f* s))(y) = Nat.card (f.inducedMap⁻¹{y}) • s(y).
```

Here `f*` is the existing full `coefficientMap f τ`, and the multiplier is
natural-number scalar multiplication in the additive coefficient group.
The degree may vary with `y`; no division or normalization is used.
`coefficientTrace_pullback_mk_apply` specializes this equation at the actual
image `[a * f.label⁻¹, f.localSpectrumMap x]` of a quotient representative.

## Every original coefficient and the comparison laws

`coefficientTraceNatTrans f hf` has direction

```text
coefficientFunctor X R ⋙ directImage f ⟶ coefficientFunctor Y R.
```

Its component is the constructed trace, as `coefficientTraceNatTrans_app`
states. `coefficientTrace_naturality` spells out its square for every morphism
of the original `Rep.{w} R G`. The underlying coefficient maps are the original
pointwise linear intertwiners. Naturality is inherited from finite-sum
linearity in the full sheaf trace, without assuming a compatibility equation.

For identity transport, finiteness is supplied locally by
`Hom.finite_inducedMap_id_fiber` and covering by
`Hom.isCoveringMap_inducedMap_id`. `coefficientTrace_id` identifies trace with
the component of `directImageIdIso.hom`. The source functor for actual rational
identity transport is compared to the identity using the previously proved
equality of continuous maps; it need not be definitionally the identity.
`coefficientTraceNatTrans_id` states the same law on the whole coefficient
category, using left whiskering of that existing comparison.

For `f : X ⟶ Y` and `g : Y ⟶ Z`, `coefficientTrace_comp` proves

```text
trace_(f ≫ g) = directImageCompIso.hom ≫ g_*(trace_f) ≫ trace_g.
```

It retains finite fibers and genuine covering for `f`, `g` and `f ≫ g`.
Composite finiteness can be supplied by
`Hom.finite_inducedMap_comp_fiber`; composite covering remains an explicit
premise. `coefficientTraceNatTrans_comp` gives the equality of natural
transformations, with the existing comparison followed by right whiskering of
trace for `f` and then trace for `g`.

The private helper `traceDirectImage_congr` substitutes equality of the
continuous maps to identify the full direct-image functors. `trace_congr`
proves the trace equation through `eqToIso` by the same substitution and proof
irrelevance. For identity, its application to `inducedMap_id_eq` is followed by
the generic identity trace and the category identity law. For composition,
its application to `inducedMap_comp_eq` is followed by the generic composite
trace law. The equality proofs defining the new transport and the existing
comparison isomorphisms agree by proof irrelevance. The natural-transformation
laws follow componentwise from these sheaf equations.

## Remaining scope

This supplies a trace on the full ordinary-open degree-zero coefficient sheaf
for actual rational transport maps satisfying the stated geometric predicates.
It establishes no general covering theorem for rational maps, smooth
coreflection specialization, etale/Godement or higher derived trace, comparison
with geometric compact-support cohomology, arithmetic Hecke identification,
Shimura-tower specialization or Harris compatibility. Those remain obligations
of the wider task; the present construction does not complete that task.
