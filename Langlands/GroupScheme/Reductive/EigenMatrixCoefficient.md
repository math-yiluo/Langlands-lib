# Matrix coefficients of eigen-covectors against eigenvectors

Worker 1628 derives this internal construction from the Library's
identification of coordinates with global functions and the point matrices of
matrix representations. For an actual matrix representation `ρ` of a group
`G` over a field `k`, a covector `ξ` and a vector `v`, it constructs the
coordinate `d(g) = ξ(ρ(g) v)` of `G`. It then proves the covariance laws that
`SteinbergBigCellStatement` asks of `d`. Left covariance comes from an
eigen-covector law for `ξ`, right covariance from an eigenvector law for `v`,
and `d(1) = 1` from `ξ(v) = 1`. The eigen-laws are explicit hypotheses on
every test scheme. The file does not construct any representation, eigenvector
or eigen-covector, and it assumes no highest-weight theory.

In the intended application, `ρ` is a representation whose highest weight is
half the sum of the positive roots. `v` spans its lowest weight line, which is
stable under the opposite Borel subgroup, and `ξ` is the projection onto that
line, an eigen-covector for the Borel subgroup. The Markdown of
`SteinbergBigCellStatement` describes these witnesses. This file uses none of
them.

## Setting

Let `k` be a field, `n` a finite index type, `G` a group scheme over `Spec k`,
`ρ : MatrixRepresentation G n` an actual matrix representation, and
`ξ v : n → k`. For a test scheme `T` over `Spec k`, `scalarMap T` maps `k` to
the global sections `Γ(T, ⊤)`, as in the Library's `IsFixedVector`, and
`ρ.pointMatrix T g` is the invertible matrix of `ρ` at a point `g ∈ G(T)`.
Covectors are row vectors, so `ξ` acts by the dot product.

## Coefficient values

- `coefficientValue ρ ξ v T g` is `ξ_T ⬝ᵥ (ρ(g) *ᵥ v_T)` in `Γ(T, ⊤)`, where
  `ξ_T` and `v_T` are `ξ` and `v` mapped by `scalarMap T`.
- `coefficientValue_naturality`: for a map of test schemes `a : T' → T`, the
  value at `a ≫ g` is the pullback along `a` of the value at `g`. Pullback of
  sections is a ring map, so it commutes with dot products and matrix-vector
  products. `pointMatrix_naturality` turns the pullback of `ρ(g)` into
  `ρ(a ≫ g)`. The scalars `scalarMap T c` pull back to `scalarMap T' c`, since
  `a` commutes with the structure maps to `Spec k`.
- `coefficientValue_one`: at the identity point the value is
  `scalarMap T (ξ ⬝ᵥ v)`, because `ρ(1)` is the identity matrix.
- `coefficientValue_mul_left`: if `ξ_T ᵥ* ρ(h) = c • ξ_T`, then the value at
  `h g` is `c` times the value at `g`. This uses `ρ(h g) = ρ(h) ρ(g)` and
  `ξ_T ⬝ᵥ (ρ(h) *ᵥ w) = (ξ_T ᵥ* ρ(h)) ⬝ᵥ w`.
- `coefficientValue_mul_right`: if `ρ(h) *ᵥ v_T = c • v_T`, then the value at
  `g h` is `c` times the value at `g`.

## The coordinate

Now assume `G.X.left` affine.

- `pointValue G T g b` is `pointAlgebraHom G T g b`, the value of a
  coordinate `b` at `g`, regarded as an element of `Γ(T, ⊤)`. It is an
  abbreviation, used to state eigenvalues in the ring of the vectors.
- `matrixCoefficient G ρ ξ v` is the coordinate whose global function, under
  the Library's `globalAlgEquiv`, is the coefficient value at the universal
  point `𝟙 G.X`.
- `pointAlgebraHom_matrixCoefficient`: the matrix coefficient evaluates to
  `coefficientValue ρ ξ v T g` at every point `g ∈ G(T)` of every test scheme.
  The Library's `pointAlgebraHom_apply_eq` writes the evaluation as the
  pullback along `g` of the global function, and `coefficientValue_naturality`
  at `g ≫ 𝟙 G.X` finishes the proof.
- `pointAlgebraHom_one_matrixCoefficient`: if `ξ ⬝ᵥ v = 1`, the matrix
  coefficient takes the value `1` at the identity point of every test scheme,
  in particular at `Over.mk (𝟙 (Spec k))`.

## Covariance

Let `H` and `H'` be group schemes over `Spec k`, all three with affine
structure morphisms, with actual homomorphisms `i : H → G` and `i' : H' → G`,
and coordinates `χ` of `H` and `ψ` of `H'`.

- `matrixCoefficient_mem_leftCovariantSubspace`: assume, for every test scheme
  `T` and `h ∈ H(T)`, that `ξ_T ᵥ* ρ(i(h)) = χ(h) • ξ_T`, with `χ(h)` the value
  `pointValue H T h χ`. Then the matrix coefficient lies in
  `leftCovariantSubspace i χ`. By the Library's
  `mem_leftCovariantSubspace_iff_points` it suffices to check
  `d(i(h) g) = χ(h) d(g)` on every test scheme, which is
  `coefficientValue_mul_left`.
- `pointAlgebraHom_mul_inv_matrixCoefficient`: assume, for every `T` and
  `h ∈ H'(T)`, that `ρ(i'(h)⁻¹) *ᵥ v_T = ψ(h) • v_T`. Then
  `d(g i'(h)⁻¹) = ψ(h) d(g)` for all points `h ∈ H'(T)` and `g ∈ G(T)` of every
  test scheme. This is `coefficientValue_mul_right` with the point
  `i'(h)⁻¹`.

With `H' = H`, `i' = i ≫ inn(n)` and `ψ = χ`, the three conclusions are
conditions 1, 2 and 3 of `SteinbergBigCellStatement`, in the forms stated
there.

## Scope

The eigen-laws are hypotheses. Producing a representation with an
eigen-covector for the Borel subgroup and an eigenvector for its opposite of
matching weights, and proving the remaining conditions of
`SteinbergBigCellStatement`, are separate obligations.
