# Orthogonal cocycle cohomology and congruence of descended forms

Worker 863.

This internal comparison identifies pairwise cohomology of finite-Galois
orthogonal matrix cocycles with congruence of their descended Gram matrices
over the ground field. It applies to any finite coordinate type, including the
empty type, and any choices of descent data from `OrthogonalCocycleDescent`.
No arithmetic hypothesis or local-to-global principle is assumed.

`gramTransform P B = P B Pᵀ` uses the row convention.
`GramCongruent B₁ B₂` means that an invertible matrix `Q` over the ground
ring satisfies `Q B₂ Qᵀ = B₁`. The supporting lemmas express composition,
inverse cancellation and coefficient extension of these transformations.

`OrthogonalCocycle.Cohomologous c₁ c₂` requires an invertible matrix `a`
over `L` preserving `H_L` and satisfying

`c₂(σ) = a⁻¹ c₁(σ) σ(a)`

for every automorphism of `L/k`. This is the same twist order as the
Library's natural group-scheme cocycles.

The main theorem `cohomologous_iff_gramCongruent` takes any two descent
records `(B₁,P₁)` and `(B₂,P₂)` for the cocycles and proves

`c₁.Cohomologous c₂ ↔ GramCongruent B₁ B₂`.

In the forward direction, the matrix `P₁⁻¹ a P₂` is fixed by the full
Galois group. `exists_unit_of_fixed` descends it entry by entry, reflecting
invertibility through its determinant. The descended matrix `Q` satisfies
`Q B₂ Qᵀ = B₁`: extend the equality to `L`, substitute the descent
identities and cancel `P₂` and its inverse before using preservation of `H_L`.
Injectivity of the field inclusion reflects the equality.

Conversely, extend a ground-field congruence `Q` to `L` and set
`a = P₁ Q_L P₂⁻¹`. The Gram identities prove that `a` preserves `H_L`.
Since `Q_L` is fixed by every automorphism, the two Hilbert 90 identities
give the required cocycle twist equation.

The provenance is internal: the proof uses the explicit descent equations
already established in `OrthogonalCocycleDescent`, Galois fixed-field descent,
and matrix and group identities. It does not yet identify these matrix
cocycles with natural group-scheme cocycles or compare their completions.
