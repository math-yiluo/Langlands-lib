# Diagonalizable averaging on coordinate coalgebras

Worker 1628. This is an internal coordinate construction for the torus projection
in the positive-characteristic conjugation-map argument. It uses the published
left and right coalgebra contractions, their commutation, and the standard
group-like basis of the additive group algebra. No cardinality average or
division is used.

For a field `k`, a `k`-coalgebra `B`, an abelian group `Λ`, and a coalgebra map
`r : B →ₗc[k] k[Λ]`, `Chevalley.diagonalizableReynolds r` is left contraction
by the zero-coordinate functional composed with `r`. The left-contraction
composition law and compatibility with `r` show that every left translation
acts on the image by evaluation at the unit of `k[Λ]`. Separation by linear
functionals promotes this assertion to the exact tensor equation
`(r ⊗ id) Δ(P b) = 1 ⊗ P b`.

The projection fixes every element satisfying this covariance equation.
Consequently its range is exactly that covariant subspace and it is idempotent.
Commutation of left and right contractions proves that the projection commutes
with every right translation. Thus the image of any right-translation-stable
subspace is still stable. When `B` is a bialgebra and `r` is a bialgebra map,
the projection fixes `1`.

For an actual affine group scheme `G` over `k`, an actual homomorphism
`j : D(Λ) → G` gives `AffineCoordinates.diagonalizableRestriction j` by
full faithfulness of the Hopf-spectrum functor and the existing actual
diagonalizable and affine-coordinate isomorphisms. Composing the preceding
construction with this restriction gives
`AffineCoordinates.diagonalizableReynolds j` on the chosen coordinate Hopf
algebra, and it fixes the unit.

The field universe is arbitrary. No centrality, finite generation or
torsion-freeness of `Λ`, reducedness, or characteristic hypothesis occurs.
This file uses the Hopf-coordinate coalgebra throughout its actual-group
specialization. Comparing this with the coalgebra chosen by
`AffineCoordinates.corepresentation` is a separate obligation; no definitional
identification is asserted. The file does not construct Steinberg modules,
prove their irreducibility or self-duality, establish tensor-square exhaustion,
or prove `SimplyConnectedPositiveCharConjugationMapStatement`.
