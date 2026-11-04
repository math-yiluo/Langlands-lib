# Actual finite subgroup restriction traces

This internal construction supplies the geometric hypotheses of the existing
ordinary coefficient sheaf trace and compact-support pullback and trace for the
original rational subgroup-restriction arrow. Covering, finiteness of every
literal fiber, properness and relative-index degree come from
`InducedRationalSubgroupCovering`.

The inputs are a complete ultrametric normed field `K : Type u`, a presented
strict affinoid algebra `P` over `K`, a topological group `G : Type v`, an
original `RationalSpectralAction G P`, open subgroups `V ≤ U`, and a
`U`-invariant rational domain `d`. The coefficient ring `R : Type r` is any
commutative ring and the coefficient carrier has universe `w`. The four
universes are independent.

Write

```text
X = (inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d),
Y = (inclusion U).obj d,
f = subgroupRestriction h d : X ⟶ Y,
D = U / (V.toSubgroup.subgroupOf U.toSubgroup).
```

Every construction in this module assumes `Finite D`. No covering,
finite-fiber, properness or action-comparison witness is an additional input.
The source and target retain the same original rational presentation and
local Banach spectrum; their subgroup actions and induced quotient spectra
are the existing ones. The map is the original `f.inducedMap`, identified in
the imported covering module with `[g,x]_V ↦ [g,x]_U`.
Its full `G`-equivariance is retained.

The local instance `finite_subgroupRestrictionFiber` transports finiteness of
`D` through the proved homeomorphism with the entire literal fiber of
`f.inducedMap`. It supplies the finite-fiber instances required by the generic
trace APIs. `properSubgroupRestriction` bundles the unchanged arrow `f` in
`ProperTransport ρ`, with properness supplied by the imported theorem.
`properSubgroupRestriction_hom` proves that forgetting this witness returns
exactly `f`.

For any original representation `τ : Representation R G M`,
`subgroupRestrictionCoefficientTrace` is the sheaf morphism

```text
f_*(L_X(τ)) ⟶ L_Y(τ).
```

Here `L_X` and `L_Y` are the full ordinary-open locally constant equivariant
coefficient sheaves, and `f_*` is the existing `SheafVariation.directImage`.
The coefficient category is `ModuleCat.{max (max u v) w} R`.
There is no topology, smoothness, dimension or admissibility assumption on
`M`. The definition is exactly `SheafVariation.coefficientTrace` at the
original arrow with its proved covering predicate, as recorded by
`subgroupRestrictionCoefficientTrace_eq`.

For `A : ActionOpens G Y.InducedSpectrum`, an original locally constant
section `s` over the inverse-image open and a point `y : A.openSet`,
`subgroupRestrictionCoefficientTrace_apply` evaluates the trace as

```text
fiberSum (DirectImage.pointMap f.inducedMap f.inducedMap_smul A) s y.
```

The restricted point map uses the original inverse-image open. Its fiber is
the entire original fiber with the corresponding open-membership proofs,
as in the imported trace construction. The sum is unnormalized.
`subgroupRestrictionCoefficientTrace_pullback_apply` proves on every such
open that pullback by the existing `SheafVariation.coefficientMap f τ`,
followed by this trace, evaluates to

```text
V.toSubgroup.relIndex U.toSubgroup • s y.
```

This is natural-number scalar multiplication. The proof substitutes the
generic literal-fiber degree formula and the proved relative-index
cardinality of that same original fiber. It does not assume a constant
degree or invert the index.

`subgroupRestrictionCoefficientTraceNatTrans` packages the trace over the
entire original `Rep.{w} R G` category. Its source is the source coefficient
functor followed by `f_*`, and its target is the target coefficient functor.
Its components are definitionally the preceding traces.
`subgroupRestrictionCoefficientTrace_naturality` states the naturality
square for every original coefficient intertwiner, using exactly the
pointwise coefficient maps of those functors.

For compact support the coefficients range over the entire original
`SmoothRep.{r, v, w} R G`. The carrier
`CompactSections.Functions X` is the full module of compactly supported
locally constant functions on the original induced spectrum with values
in the original coefficient module. Its diagonal full-group action is
the already constructed smooth action

```text
(g • s)(z) = M.representation g (s(g⁻¹ • z)).
```

No local stable-neighbourhood premise is required for this compact-support
representation.

`subgroupRestrictionCompactSupportPullback` uses the proved properness
of `f.inducedMap` to give a morphism from the compact representation on `Y`
to that on `X`. `subgroupRestrictionCompactSupportPullback_apply`
identifies its value with `s.val (f.inducedMap z)`.
`subgroupRestrictionCompactSupportTrace` gives the reverse morphism using
the proved covering and finite fibers.
`subgroupRestrictionCompactSupportTrace_apply` identifies its value with
`fiberSum f.inducedMap s.val y`.
The full carriers, compact support and original diagonal actions are
retained by the generic constructions.

With a `Fintype D` instance,
`subgroupRestrictionCompactSupportTrace_apply_sum` presents this same
trace as the sum over every relative coset:

```text
∑ c : D, s.val (subgroupRestrictionFiberHomeomorph h d y c).val.
```

The reindexing equivalence identifies `D` with the entire original literal
fiber. It uses the chosen homeomorphism of the covering module; no
equivariance of that chosen chart is asserted. `Finite D` suffices for
the construction; the `Fintype` instance only displays the finite sum.
`subgroupRestrictionCompactSupportTrace_pullback_apply` proves that
proper pullback followed by this trace evaluates to
`V.toSubgroup.relIndex U.toSubgroup • s.val y`.
The proof uses `fiberSum_comap` and the same proved original-fiber
cardinality.

`subgroupRestrictionCompactSupportPullbackNatTrans` and
`subgroupRestrictionCompactSupportTraceNatTrans` package the two maps
between the existing coefficient functors in opposite directions.
Their domain category is `SmoothRep.{r, v, w} R G` and their codomain
category is `SmoothRep.{r, v, max u v w} R G`. The component lemmas identify
them definitionally with the maps just described. Thus both operations
commute with every original smooth coefficient intertwiner.

The provenance is internal. The module specializes
`InducedRationalSheafTrace`, `InducedRationalCoveringTrace` and the existing
proper compact-support pullback to the original subgroup arrow.
`InducedRationalSubgroupCovering` proves the required geometric predicates,
entire-fiber homeomorphism and numerical index formula. The generic
trace and compact-support constructions prove their sheaf, linearity,
support and equivariance obligations. The new degree proofs substitute
the actual index equality, and the coset sum reindexes the whole actual
fiber. No external theorem from Harris or Berkovich is claimed.

This unit concerns subgroup change with the rational presentation fixed,
ordinary-open degree-zero coefficient sheaves, and compactly supported
locally constant functions. Smooth ordinary-open sheaf specialization,
general rational-domain coverings, analytic or etale trace, derived
compact-support comparison, arithmetic Hecke identification, Shimura
specialization and Harris compatibility remain obligations of the broader
task.
