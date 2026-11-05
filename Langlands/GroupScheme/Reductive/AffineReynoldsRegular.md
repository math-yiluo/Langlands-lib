# Diagonalizable-invariant regular maps for actual affine groups

Worker 1330 derives this actual-coordinate specialization of Worker 1628's
Reynolds construction. Its internal inputs are the existing affine coordinate
isomorphisms and evaluation laws, the diagonalizable Hopf-coordinate restriction,
and the finite normalized Reynolds coefficient construction. No external
representation-theoretic assertion enters these comparisons.

Let `k : Type u` be any field, let `G` be a group scheme over `Spec k` whose
underlying scheme is affine, and let `Λ : Type u` be an abelian group. An actual
group-scheme homomorphism `j : D(Λ) → G` determines
`AffineCoordinates.corepresentationDiagonalizableRestriction`. This is a
bialgebra map from the coordinate algebra of `G`, equipped with the coalgebra
used by its regular representation, to the standard group algebra `k[Λ]`.
The construction retains the algebra map of `diagonalizableRestriction j`
and transports its two coalgebra laws through `corepresentation_counit` and
`corepresentation_comul`. Its underlying algebra map is unchanged, as stated
by `corepresentationDiagonalizableRestriction_toAlgHom`.

`algSpec_map_diagonalizableRestriction` identifies the relative spectrum of
that algebra map with the actual morphism `j`, conjugated by the existing
coordinate isomorphisms. The proof uses full faithfulness of Hopf spectrum and
the comparison of the two affine coordinate isomorphisms.
`pointAlgebraHom_diagonalizableRestriction` then applies the relative spectrum
adjunction's naturality: evaluating a coordinate at `j(h)` is evaluating its
restriction at `h`. Here `h` is a point over an arbitrary scheme over `Spec k`;
no affineness or reducedness condition is imposed on the test scheme.

`pointAlgebraHom_diagonalizableInvariant` contracts the tensor identity
`(r ⊗ id) Δ(w) = 1 ⊗ w` with evaluation at `h` and `g`. The evaluation formula
for multiplication and the preceding restriction formula give
`w(j(h) * g) = w(g)` on every scheme test. The tensor-factor order is left
multiplication by the diagonalizable point followed by the arbitrary group
point.

`Chevalley.exists_affine_finite_diagonalizable_regular_map_to_one` takes an
actual finite matrix representation `ρ` of `G` and a nonzero vector `v` fixed
on every scheme test. It constructs a finite coordinate subspace `V`, a basis
indexed by `Fin d`, stability under every right contraction, and a matrix `C`
intertwining `ρ` with the actual representation
`affineRegularRepresentation G V b hV`. Every `w` in `V` satisfies both the
preceding tensor identity and its left-invariance equation on every scheme
test. The coordinates of `C *ᵥ v` in that basis reconstruct the constant
function `1`.

The proof restricts `ρ` through the affine coordinate isomorphism, applies
`exists_finite_diagonalizable_regular_map_to_one` to the transported actual
restriction, and transports the resulting intertwiner back to `G`. This
intertwiner is quantified over every commutative algebra test, including
nonreduced algebras. The existing `MatrixRepresentation.Intertwines.points`
also gives its equation on every scheme test. The final normalization equation
and the covariance tensor equation survive the transport unchanged; the
all-scheme invariance follows from the contraction theorem above.

All declarations retain arbitrary field universe `u`. The character group may
have torsion and need not be finitely generated. The construction requires no
characteristic, reductivity, simple connectedness or centrality hypothesis.
It does not construct Steinberg modules or establish irreducibility,
self-duality, tensor-square exhaustion or the final positive-characteristic
conjugation-map existence proposition.
