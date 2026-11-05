# Multiplication of covariant coordinate spaces

Worker 1330 derives this internal construction from standard bialgebra
identities: comultiplication is an algebra homomorphism, and the regular
representation on a finite stable coordinate subspace is read off from its
coaction matrix. It implements multiplication of regular functions, as needed
when products of induced modules are formed inside the coordinate algebra, for
example in the multiplication of sections used in Mumford–Fogarty–Kirwan,
Appendix 1.A. It does not assert injectivity of multiplication, irreducibility
of an induced module, or exhaustion of torus-invariant coordinates.

## Coordinate products

Let `k` be a field and `B` a commutative `k`-algebra. For subspaces `V` and `W`
of `B`, `coordinateProduct V W` is the linear map `V ⊗ W → B` sending `v ⊗ w`
to `v * w` (`coordinateProduct_tmul`). `range_coordinateProduct` states that
its image is exactly the product submodule `V * W`.
`finite_coordinateProduct` concludes that `V * W` is finite-dimensional when
`V` and `W` are.

Given bases `bV`, `bW` and `bP` of `V`, `W` and `V * W`, indexed by `Fin a`,
`Fin b` and `Fin c`, `productMatrix V W bV bW bP` is the `Fin c` by
`Fin a × Fin b` scalar matrix whose `(i, (l₁, l₂))` entry is the `i`-th
`bP`-coordinate of `bV l₁ * bW l₂`. The coordinate is computed by the existing
`extendedCoord`, which retracts `B` onto `V * W` before taking the coordinate.
On basis products this is the matrix of `coordinateProduct V W`.

## Covariance weights multiply

Now let `B` be a commutative bialgebra over `k`, `C` a commutative `k`-algebra,
and `r : B → C` an algebra homomorphism. `mul_mem_leftCovariantSubspace`
states that if `v` and `w` lie in the left-covariant subspaces of `r` with
coordinates `χ` and `ψ`, then `v * w` lies in the left-covariant subspace with
coordinate `χ * ψ`. The proof applies `(r ⊗ id)` to `Δ(v * w) = Δ(v) Δ(w)`,
uses that `r ⊗ id` is multiplicative, and multiplies the two equations
`(r ⊗ id) Δ(v) = χ ⊗ v` and `(r ⊗ id) Δ(w) = ψ ⊗ w`. No character or
group-like property is assumed for `χ` or `ψ`.
`mul_le_leftCovariantSubspace` gives the same conclusion for the product of
two subspaces contained in those covariant subspaces.

For an actual affine group-scheme morphism `i : H → G` over `Spec k`, both
group schemes having affine structure morphisms,
`AffineCoordinates.mul_mem_leftCovariantSubspace` and
`AffineCoordinates.mul_le_leftCovariantSubspace` state the same two facts for
the actual covariant subspace `AffineCoordinates.leftCovariantSubspace i χ`.
They specialize the general theorems to the coalgebra used by the regular
representation and to the actual pullback algebra map of `i`.

## Products of regular subspaces

Assume `V` and `W` are stable under every right contraction `rightAct f`, with
`f` a linear functional on `B`. For basis vectors, `comul_basis_mul` states

`Δ(bV i * bW j) = ∑_{(l₁, l₂)} (bV l₁ * bW l₂) ⊗ (M_V l₁ i * M_W l₂ j)`,

where `M_V` and `M_W` are the existing `subspaceMatrix` coaction matrices. It
follows from multiplicativity of comultiplication and the basis coaction
formulas for `V` and `W`. Contracting the right tensor factor with `f` gives
`rightAct_basis_mul`. `rightAct_mem_mul` then proves that, when `V` and `W` are
finite-dimensional, `V * W` is again stable under every right contraction. The
proof expands arbitrary elements of `V` and `W` in finite bases and inducts on
membership in `V * W`.

`affine_rightAct_mem_mul` states this stability for coordinate subspaces of an
affine group scheme `G` over `Spec k`, with the regular-representation
coalgebra, given finite bases of `V` and `W`.

## Multiplication is an actual intertwiner

Let `B` corepresent an actual group functor `F` on commutative `k`-algebras.
`universalMatrix_tensor` states that the universal matrix of the actual tensor
product of two matrix representations is the entrywise product of the two
universal matrices; it is the existing `tensor_affineMatrix_entry` at the
universal point.

`intertwines_productMatrix` states that `productMatrix V W bV bW bP`
intertwines the actual tensor product of the regular representations on `V`
and `W` with the regular representation on `V * W`. All three
representations are the existing actual `regularRepresentation`; stability of
`V * W` is an explicit hypothesis `hP`, which `affine_rightAct_mem_mul`
supplies for affine groups. By `intertwines_of_universalMatrix`, it suffices to
check the equation at the universal point. There the tensor matrix is the
product of the two coaction matrices, and `coactionCoordinates_mul` with
`comul_basis_mul` gives the equation. The conclusion is the actual
`Intertwines` equation on every commutative algebra test, including nonreduced
algebras.

For an affine group scheme `G` over `Spec k`,
`intertwines_affine_productMatrix` states the same intertwining equation for
the representations `affineRegularRepresentation G V bV hV`,
`affineRegularRepresentation G W bW hW` and
`affineRegularRepresentation G (V * W) bP hP`. The proof restricts the
corepresented intertwiner through the inverse of
`AffineCoordinates.groupSchemeIso G` with `Intertwines.restrict`, then uses
`tensor_restrict` to identify the restricted tensor product with the tensor
product of the two restrictions.

All declarations retain the arbitrary universe `u` of the field and the test
algebras. No characteristic, reductivity, simple connectedness, properness or
highest-weight hypothesis is used. Nothing here constructs Steinberg modules,
proves that multiplication is injective or surjective onto a given space, or
establishes the positive-characteristic conjugation-map proposition.
