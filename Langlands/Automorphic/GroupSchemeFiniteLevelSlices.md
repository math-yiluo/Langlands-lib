# Finite-level reconstruction on actual adelic group-scheme points

This internal construction adapts the public
`Langlands.Automorphic.FiniteLevelSlices` construction to the actual affine
group-scheme point groups. Worker 94 supplies the actual-point adaptation;
Worker 72's local open-coset continuity argument is retained. The base is any
number field `F : Type u`, and `G` is an affine group scheme over `Spec F`.
The original adelic point groups, rational map, factor projections, pairing,
function carriers and positive right action are unchanged.

`InfinitePlotSmoothFunctions` is a transparent alias for the existing complex
submodule `G.plotSmoothFunctions` in the original mixed archimedean coordinates.
`evaluatePlotSmoothSlices` evaluates the slice indexed by the actual finite
projection at the actual infinite projection. Evaluation on `pair a b` recovers
the value of slice `b` at `a`.

`finiteLevelPlotSmoothSliceFamilies L` is the complex submodule of families of
these actual smooth functions satisfying two explicit conditions. Every element
of the specified open finite subgroup `L` fixes the entire family on the right.
For every actual rational point `γ`, finite point `b` and infinite point `a`,
the slice indexed by `finite(rational γ) * b`, evaluated at
`infinite(rational γ) * a`, equals the slice indexed by `b` at `a`.
No compactness of `L` is assumed.

Reconstruction requires `SmoothOfRelativeDimension d G.X.hom`, which supplies
the previously constructed actual infinite adelic manifold. Its proved
ordinary-smoothness criterion makes each original plot-smooth slice continuous.
Near any full adelic point `x`, the inverse image of the open finite coset
`finite(x) L` is open and the family is constant in its finite index. The
reconstructed function there agrees with one fixed continuous infinite slice
composed with the continuous infinite projection. This proves joint continuity
without assuming any topology or parameter smoothness on the family itself.

`reconstructContinuousPlotSlices` uses the stated rational covariance to
construct an element of the original `ContinuousRationalFunctions`.
`reconstructFinitePlotSmoothSlices` retains infinite plot smoothness and the
same common open finite stabilizer, giving an element of the unchanged
`FinitePlotSmoothRationalFunctions`. Both maps are complex linear.

`finitePlotSmoothSlice` extracts the original smooth slice by the original
`infiniteSlice` map. The extraction of a reconstructed family is exactly that
family at every finite point. `finitePlotSmoothSlice_injective` proves that all
these slices determine the actual adelic function, using the original identity
`pair (infinite x) (finite x) = x`. `plotSlicesAtLevel` extracts a rationally
covariant family at any specified open finite subgroup fixing a given original
finite-smooth function. `reconstruct_plotSlicesAtLevel` recovers that very
function. Thus the construction uses actual function values and never assumes
an abstract reconstruction or covariance conclusion.

This unit supplies reconstruction for descending actual differential operators.
It does not yet define their adelic action, prove Lie-bracket or enveloping
compatibility, assert derivative growth, or construct a quotient measure or
an `L2` realization. The algebraic relative-dimension premise is explicit;
the existing connected-reductive theorem can supply it. No reduction or
finite-volume theorem is used.
