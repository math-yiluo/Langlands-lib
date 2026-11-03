# Block-determinant characters and eigenvalues of central derived points

Author: Worker 1408.

This internal helper module bounds the eigenvalues of a central rational point
of an actual derived subgroup. Its role is that of the weight-block determinants
in the proof of Milne, *Algebraic Groups* (2017), Proposition 12.46(a),
printed pp.245–246. The implementation is a derived, internal argument that
works with one eigenvalue at a time. It uses no torus or weight decomposition.
Namespace: `Langlands.GroupScheme.CentralIntersection`.

## The block-determinant character

Fix a commutative ring `R`, a group scheme `G` over `Spec R`, a matrix
representation `ρ : MatrixRepresentation G n` and a coefficient matrix
`π ∈ Mat_n(R)`. For a test scheme `T` over `Spec R`, `scalarMap T` sends
coefficients in `R` to `Γ(T, ⊤)`.

- `toBase T : T ⟶ Over.mk (𝟙 (Spec R))` is the structure map.
  `pointMatrix_toBase` says that the matrix of the pullback `toBase T ≫ x` of a
  rational point `x` is the image under `scalarMap T` of the rational matrix of
  `x`. `scalarMap_base` says that on `Spec R` itself, `scalarMap` followed by
  `Γ(Spec R) ≅ R` is the identity.
- `blockMatrix ρ π T g = ρ_T(g) π_T + (1 - π_T)`, where `π_T` is the image of
  `π` in `Mat_n(Γ(T, ⊤))`. `blockMatrix_naturality` gives compatibility with
  pullback along test morphisms `T' ⟶ T`.
- Assume that `π` is idempotent (`hπ`) and that `π_T` commutes with `ρ_T(g)` for
  all `T` and `g` (`hcomm`). Then `blockMatrix_mul` shows
  `blockMatrix (g h) = blockMatrix g · blockMatrix h`. Expanding the product
  uses `π_T² = π_T`, `(1 - π_T)² = 1 - π_T`, `π_T (1 - π_T) = 0` and
  commutativity. With `blockMatrix 1 = 1`, this gives the monoid homomorphism
  `blockMonoidHom`.
- `blockDetPoints T` composes the units of `blockMonoidHom` with the
  determinant and the identification `Gm.pointsEquiv` of the points of `𝔾_m`
  with units. `blockDetPoints_val` computes its value as `det (blockMatrix g)`.
  Naturality (`blockDetPoints_naturality`) follows from
  `blockMatrix_naturality` and `RingHom.map_det`.
- `blockCharacter := homOfPoints (blockDetPoints hπ hcomm) _ : G ⟶ 𝔾_m` is the
  resulting homomorphism of group schemes. `comp_blockCharacter` evaluates it on
  points.

`commute_map_aeval`: if a ring homomorphism `F` from matrices over a field `K`
sends scalar matrices to elements commuting with `b`, and `F A` commutes with
`b`, then `F (P(A))` commutes with `b` for every polynomial `P`. The proof is by
induction on `P`.

## Eigenvalues of central derived points

Let `K` be algebraically closed. Let `d : D ⟶ G` satisfy `IsDerivedSubgroup d`
and let `ρ` be any matrix representation of `G`.

`exists_pow_eq_one_of_isRoot_charpoly`: let `y` be a `K`-point of `D` such that
`x = y ≫ d` lies in the centre `center G` at the base test scheme. If `c` is a
root of the characteristic polynomial of the rational matrix `A₀` of `x`, then
`c^a = 1` for some `1 ≤ a ≤ card n`.

Proof. `exists_blockProjector` (module `LinearAlgebra`) gives a polynomial `P`
with `π = P(A₀)` idempotent and `det (A₀ π + (1 - π)) = c^a`. Centrality of `x`
says that the pullback `toBase T ≫ x` commutes with every point `g` of `G` over
every `T`. Applying `ρ_T` and `pointMatrix_toBase`, the image of `A₀` commutes
with `ρ_T(g)`. The image of a scalar matrix is scalar. So `commute_map_aeval`
shows that `π_T` commutes with `ρ_T(g)`. This is the hypothesis of
`blockCharacter`. By the published `IsDerivedSubgroup.characterRestrict_eq_zero`
(module `Derived.KernelAnnihilation`), every character of `G` restricts
trivially to `D`. So `d ≫ blockCharacter = 1` and hence
`x ≫ blockCharacter = 1`. Evaluating with `comp_blockCharacter` and
`blockDetPoints_val` shows that `det (blockMatrix x) = 1` in `Γ(Spec K)`.
Transporting along `Γ(Spec K) ≅ K` gives `det (A₀ π + (1 - π)) = 1`, using
`rationalMatrix_apply` and `scalarMap_base`. Hence `c^a = 1`.

`pow_factorial_eq_one_of_mem_roots`: under the same hypotheses, every root `c`
satisfies `c^((card n)!) = 1`, since `a` divides `(card n)!`.
