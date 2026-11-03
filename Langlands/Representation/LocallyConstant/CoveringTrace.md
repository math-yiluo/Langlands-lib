# Equivariant trace on the full compact-support modules

This internal construction restricts the actual finite-fiber trace to the
existing full compact-support locally constant modules and their original
diagonal group actions.

The coefficient ring `R : Type uR` is commutative. The group
`G : Type uG`, coefficient carrier `V : Type uV`, and space universe `uX`
are independent. The source and target spaces, and the optional composition
target, share `uX`; the function carriers have universe `max uX uV`.
Coefficients carry no topology. The algebraic intertwiner assumes spatial
actions whose individual translations are continuous. For smooth
representations, `G` is a topological group, the spatial actions are jointly
continuous, and the coefficient representation is smooth. Neither local
compactness, separation, nor compactness of the whole spaces is required.

`traceLinear` restricts `LocallyConstantCovering.traceLinearMap` to the
existing `CompactSupport.Functions R X V`. Its codomain restriction uses
`hasCompactSupport_trace`. Thus its carrier contains every compactly
supported locally constant function; there is no additional stabilizer or
invariance condition. Its evaluation is the sum over the entire actual
fiber, including zero on an empty fiber. The map is unnormalized and
requires no properness hypothesis.

For an equivariant covering map `q` with finite fibers,
`traceIntertwiner` intertwines the original representations with formula

```text
(g · f)(x) = ρ(g)(f(g⁻¹ · x)).
```

The proof first commutes the coefficient operator `ρ(g)` with the finite
sum, then reindexes the spatial translation by the actual fiber
equivalence from the topology module. No replacement action is introduced.
`smoothTrace` bundles this intertwiner between the full compact-support
smooth representations already constructed in `CompactSupport`.

`smoothTrace_naturality` uses the original pointwise coefficient maps.
Their commutation with trace is the finite-sum linear-map identity
`trace_map`. `traceNatTrans` therefore retains every smooth coefficient
object and intertwiner as a natural transformation between the existing
`coefficientFunctor`s.

`smoothTrace_id` evaluates on each point and uses the actual one-point
identity fiber. `smoothTrace_comp` partitions the composite fiber by its
intermediate points, using `fiberSum_comp`. It states covariant
composition in the original maps. Besides the finite-fiber instances, its
premises explicitly require that both maps and their original composite
are covering maps. No automatic covering-composition assertion is made.

The provenance is internal: restrict the constructed finite sum using its
proved support containment, prove intertwining by the original group
action, and reuse the existing smoothness theorem for the full
compact-support module. This is a construction on ordinary locally
constant functions. It does not supply higher sheaf-derived or etale trace,
Godement acyclicity, arithmetic coefficient systems, or the Harris
specialization.
