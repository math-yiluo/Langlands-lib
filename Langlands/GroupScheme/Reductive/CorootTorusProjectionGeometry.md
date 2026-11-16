# Split product geometry of the coroot torus projection

This derived construction continues the torus step of Conrad, *Reductive Group
Schemes* (2014), Theorem 5.3.1, printed pp.160–163. Write `M = I → ℤ` and let
`L = cocenterLattice P` be the integral annihilator of every coroot. The source's
coroot-generated subtorus is `D(M/L)`, while its torus quotient is `D(L)`.
The product decomposition below is an internal way to establish the geometry of
the previously constructed projection; it does not extend it to the ambient
reductive group.

For a finite root index type `J`, `free_quotient_corootAnnihilator` proves that
`M/L` is a free integer module. Projectivity supplies a chosen linear section
`corootLatticeSection` of the quotient map. Adding an element of `L` to a chosen
lift of an element of `M/L` gives the linear equivalence
`corootLatticeSplit : L × (M/L) ≃ₗ[ℤ] M`. Injectivity follows by applying the
quotient map and then cancelling the common lift; surjectivity follows by
subtracting the lift of an element's quotient class. Its restriction to `(m,0)`
is the original inclusion of `L`. This splitting is chosen, with no claim of
canonicity.

The generic lemma `Diagonalizable.productIso_hom_fst` records the first
coordinate of the published product isomorphism for diagonalizable groups.
On every test scheme it evaluates a character at `(a,0)`. It follows directly
from the defining point-model comparison of that isomorphism.

For finite `I`, finite `J`, and any commutative coefficient ring `R`,
`corootSubtorus R P` is the actual group scheme `D(M/L)`. A basis of its free
finite-rank character lattice proves that it is a split torus.
`corootProjectionProductIso` combines the coordinate-torus comparison, the
chosen lattice splitting, and the diagonalizable product comparison to give
an actual group-scheme isomorphism

`splitTorus (Spec R) I ≅ D(L) × D(M/L)`.

`corootProjectionProductIso_fst` proves equality of the underlying morphism
obtained by first projection with the previously constructed
`corootProjection`. The proof uses Yoneda and the injective character-point
comparison, then the product and lattice-isomorphism character formulas.
The identity on `(m,0)` reduces this to the character-restriction formula.

`smooth_corootProjection` transfers smoothness of the first product projection
through this isomorphism; its second factor is the split torus just constructed.
`surjective_corootProjection` uses the section of first projection given by the
identity in the second factor and then the isomorphism. These conclusions hold
over arbitrary rings, including nonreduced rings and the zero ring, with no
additional condition on the root-datum pairing. They concern the maximal torus
map only; multiplicativity of the big-cell map and semisimplicity of a kernel in
the full reductive group remain separate obligations.
