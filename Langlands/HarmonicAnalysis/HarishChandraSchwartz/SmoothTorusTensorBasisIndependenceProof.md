# Independence of the finite coefficient basis

`Langlands.HarishChandraSchwartz.smoothTensorBasisIndependence` proves
`Langlands.HarishChandraSchwartz.SmoothTensorBasisIndependenceStatement`.
For any finite torus coordinate type `J` and two finite bases of a complex
vector space `V`, it identifies the two finite-product topologies on the same
algebraic tensor `smoothFiniteTorusFunctions J ⊗[ℂ] V`. The torus coordinates,
the coefficient space and the two basis index types have independent universes.

This is an internal basis-independence result for the product topology in
Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, VI.3, printed p. 301, PDF p. 67. There the scalar
space has its usual smooth topology and the fixed compact-picture
coefficient space is finite dimensional. VI.1, printed pp. 295–296,
PDF pp. 61–62, describes the smooth families and their tensor realization.
The registered source is `waldspurger-2003-plancherel`.
[Waldspurger 2003](https://doi.org/10.1017/S1474748003000082)

The proof evaluates the `k`th scalar coordinate in basis `c` at a point of
the torus. By `smoothTensorCoordinates_apply` this is the `k`th coordinate
of the tensor's value in `V`. Applying `Module.Basis.sum_repr_mul_repr` to
that value expresses the scalar function as the sum of the coordinates in
basis `b`, each multiplied by the constant `c.coord k (b i)`.

With `smoothTorusFunctionTopology J` installed locally, the ordered
derivative seminorm family gives `WithSeminorms` by definition. Its
topological additive group and continuous scalar multiplication properties
make finite sums of constant multiples of continuous scalar-coordinate maps
continuous. Projection from the product for `b` and the initial continuity
of `smoothTensorCoordinates J b` therefore give continuity of every
coordinate in `c`. This is continuity of the entire coordinate map into the
product for `c`, so the pullback topology for `b` is at most that for `c` in
Lean's topology order. Interchanging the bases gives the reverse inequality
and `le_antisymm` gives equality.
