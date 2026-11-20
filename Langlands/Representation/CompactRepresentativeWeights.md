# Dense scalar weights with finite left-translation orbit

This internal prerequisite concerns continuous complex functions on a topological
group. The original left regular action is `g • f(k) = f(g⁻¹ k)`. A function is
finite if its actual translation orbit spans a finite dimensional complex vector
space, using the published `Langlands.FiniteVectors.IsFiniteVector`.

These functions form the star subalgebra `finiteWeights`. The product orbit lies
in the product of the two orbit spans. Finite generation of the two spans gives
finite generation of their product, hence finite dimensionality. Pointwise
conjugation commutes with translation, so the orbit span of the conjugate function
lies in the finitely generated semilinear image of the original orbit span.
Each translate of the constant one lies in its one-dimensional span. Scalar
multiples of one give all constants, and the finite-vector lemmas give closure
under addition and scalar multiplication.

Let `τ` be a supplied faithful representation of the group on `ι → ℂ` for a
finite index type `ι`. Continuity of each original orbit map `k ↦ τ k v`
gives continuity of the inverse coefficient `k ↦ τ (k⁻¹) v j` by composition
with inversion and coordinate evaluation. For each `j`, the map sending `v`
to this coefficient intertwines `τ` with left translation because
`τ ((g⁻¹ k)⁻¹) = τ (k⁻¹) * τ g`. Every vector in `ι → ℂ` is finite, and
the intertwiner preserves finiteness. If all these coefficients agree at two
points, their inverses act identically on all vectors. Injectivity of `τ` and
of inversion then makes the two points equal.

On a compact group, Mathlib's complex Stone-Weierstrass theorem identifies the
closure of this separating star subalgebra with the full algebra `C(K, ℂ)`.
The topology of `C(K, ℂ)` for compact `K` is the uniform topology, so this
gives uniform density.

`CompactRepresentativeWeightsStatement` records this density result with both
the group and finite index type universes free. `compactRepresentativeWeights`
proves that proposition. This internal result supplies scalar weights for the
compact approximation route of Task 7293. The argument combines the Library's
finite-vector construction with Mathlib's Stone-Weierstrass theorem on the
explicit hypothesis of a faithful representation with continuous vector orbits.
