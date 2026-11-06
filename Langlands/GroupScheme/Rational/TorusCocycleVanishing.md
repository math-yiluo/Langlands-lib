# Triviality of torus cocycles on finite Galois covers

`Langlands.GroupScheme.HasTrivialTorusCocycles K` is an internal field
property for an arbitrary field `K : Type u`. For every actual group
scheme `T` over `Spec K` satisfying the existing `IsTorus T`, every finite
Galois extension `L/K` in `Type u`, and every actual `Cocycle T U` on
`U = Spec L → Spec K`, it asserts `Cocycle.IsTrivial`.

The imported [torus definition](../Torus/Lattice.md) means that `T`
becomes a finite product of multiplicative groups after an actual field
base change. The imported [cocycle formalism](../TorsorCocycle.md) uses
natural families on pairs of maps `a, b : Z → U` over **all** test schemes
`Z` over `Spec K`. The cocycle identity is
`ξ(a,c) = ξ(a,b) * ξ(b,c)`. Triviality gives an actual morphism
`f : U → T` over `Spec K` for which
`ξ(a,b) = f(a) * f(b)⁻¹` for every such test pair.

Thus this property refers to actual scheme cocycles and actual
coboundaries. It is not a replacement definition of `IsTorus`, of the
norm criterion, or of quasi-splitness. It adds no splitness requirement
on `T` over the chosen `L`. Finite Galois covers suffice for smooth
torsors split by finite separable extensions after passing to a finite
Galois normal closure; this module does not prove that reduction or a
cohomology comparison.

This is a derived internal interface for the torus-cohomology portion of
Steinberg's theorem, expressed entirely in the existing scheme APIs.
There is no external theorem claimed by this definition. Worker 1333
authored the interface; the existing Čech constructions are imported
from Worker 1515's published module without modification.
