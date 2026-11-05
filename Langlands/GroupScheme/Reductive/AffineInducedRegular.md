# Covariant coordinates for actual affine group morphisms

Worker 1330. This derived interface uses the existing affine coordinate
algebra, its evaluation on scheme tests, the covariance kernel, and finite
regular representations. It uses no external representation-theoretic input.

Let `k` be any field and let `i : H ⟶ G` be an actual morphism of group schemes
whose structure morphisms to `Spec k` are affine. Write `B` and `C` for their
chosen coordinate algebras. The comultiplication on `B` is explicitly the one
from `AffineLinearEmbedding.bialgebra (AffineCoordinates.corepresentation G)`.
The linear restriction map is the algebra map underlying the actual Hopf
pullback `AffineHomImageHopfAdapter.pullback i`.

`AffineCoordinates.leftCovariantSubspace i χ` is the kernel of
`(r ⊗ id) ∘ Δ - (b ↦ χ ⊗ b)`, where `χ : C` is any coordinate. No character,
subgroup or injectivity hypothesis is needed. The membership theorem exposes
exactly the tensor equation `(r ⊗ id) Δ(b) = χ ⊗ b` by the existing kernel
membership lemma, with the coalgebra instance fixed as above.

`pointAlgebraHom_leftCovariant` contracts that equation against evaluation at
`h : T ⟶ H.X` and `g : T ⟶ G.X`. Multiplication of coordinate evaluations and
compatibility with the actual Hopf pullback give
`b(i(h) * g) = χ(h) * b(g)`. This holds for every scheme `T` over `Spec k`,
including nonaffine and nonreduced tests. The proof uses linearity and the
tensor-product product map; it makes no density assumption.

`exists_finite_leftCovariant_regularSubspace` contains any supplied finite set
of covariant coordinates in a finite-dimensional subspace of `B` which is
still covariant and stable under every right contraction. It specializes the
existing finite regular-span construction. It does not assert that the whole
covariant subspace is finite dimensional.

For any affine `G`, finite regular subspace `V`, finite basis `b`, and the
stated stability under right contractions,
`Chevalley.affineRegularRepresentation_pointMatrix` identifies the actual
representation matrix on every scheme test with evaluation of the coordinate
coaction matrix. `affineRegularRepresentation_mul_basis` then expands
`b_j(g * h)` as the sum of `b_i(g)` times the `i,j` entry of that representation
at `h`. The proofs use the existing restricted regular representation and the
basis expansion of coordinate comultiplication, preserving the multiplication
order.

The field universe is arbitrary. This support construction proves no
Steinberg-module existence, irreducibility, self-duality, exhaustion, or
positive-characteristic conjugation-map existence theorem.
