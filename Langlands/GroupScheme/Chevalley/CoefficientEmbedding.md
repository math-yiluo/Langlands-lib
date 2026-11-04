# Coefficient embeddings into finite regular representations

This internal derived construction uses the published actual matrix
representations, their universal coefficients and finite regular subspaces.
It works over any field `k : Type u` for any group functor corepresented by
an actual commutative `k`-algebra `B`. No finite-type, smoothness,
connectedness, characteristic, perfection or splitting assumption is used.
All finite coordinate sets, including the empty set, are allowed.

For a finite regular subspace `V` of `B` with basis `b : Basis (Fin d) k V`,
`coactionCoordinates V b a` is the matrix whose `(i,j)` entry is the extended
`i`th basis coordinate of `a j`. For a family contained in `V` satisfying
`Δ(a j) = ∑ l, a l ⊗ M l j`, `coactionCoordinates_mul` proves the matrix
identity `E_B M = M_V E_B`. Here `M_V` is the published regular-subspace
matrix and `E_B` is scalar extension of the coordinate matrix to `B`.
The proof applies the left contraction by each extended coordinate to the
coaction equation and to the basis expansion of `a j`.

`intertwines_of_universalMatrix` proves that an intertwining matrix identity
at the actual universal point implies `MatrixRepresentation.Intertwines`.
Every affine point of the corepresented group is classified by an algebra
map `B → S`. Naturality evaluates both representation matrices by this map;
applying it entrywise to the universal equality proves the required equality
for that affine test. Thus equivariance holds for every commutative affine
test algebra, including nonreduced algebras. No rational-point density
argument enters. `regularRepresentation_universalMatrix` identifies the
universal matrix of the published actual regular representation with its
constructed subspace matrix by the corepresenting equivalence.

`intertwines_tensor_trivial` combines a finite family of equivariant maps
`C t : ρ → τ` into a map from `ρ` to `τ` tensored with the trivial
representation on the row index set. Its coefficient at `((i,t),j)` is
`C t i j`. The tensor coefficient formula and the identity matrix of the
trivial action reduce its equivariance to that of each `C t`.

For an actual representation `ρ` with universal coefficient matrix `N`,
`coefficientEmbedding e ρ V b` has entry
`E ((l,i),j) = extendedCoord V b l (N i j)`.
If `V` is stable under every right contraction and contains every entry of
`N`, `intertwines_coefficientEmbedding` makes this an actual intertwiner
from `ρ` into `regularRepresentation(V)` tensored with the trivial
representation on the original coordinate set. The universal coaction law
for each fixed row of `N` supplies the coordinate intertwining identity;
the preceding family construction combines all rows.

`coefficientEmbedding_injective` uses only containment of all coefficient
entries in `V`. A vector in the kernel has zero extended coordinates in
every row. Basis expansion then gives `∑ j, v j • N i j = 0` for every
`i`. Applying the actual coordinate counit, which evaluates `N` to the
identity matrix, gives `v i = 0`. Thus the linear map defined by `E` is
injective, with no nonempty-coordinate premise.

Finally, `exists_finite_regular_embedding` takes the regular span of the
finite set of all entries of `N`. The published finite-regular-span theorem
provides a finite-dimensional stable subspace and its finite basis. The
previous two results yield an equivariant injection into finitely many
copies of this finite regular representation.

The content is derived from the imported interfaces and elementary tensor
and coordinate identities, rather than a newly cited structural theorem.
It constructs an embedding for representations of a corepresented group.
The ambient subquotient extension theorem for a closed subgroup, unconditional
reflection of geometric semisimplicity and Cartan generation remain
separate proof obligations.
