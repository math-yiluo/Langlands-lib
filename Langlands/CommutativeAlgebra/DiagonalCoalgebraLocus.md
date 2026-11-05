# Basic open certificates for diagonal bialgebra surjectivity

This internal construction supports the affine closed-immersion locus for a
homomorphism with split torus source. Scalar extension takes an algebra map
`B → R[M]` to the actual algebra map `A ⊗[R] B → A[M]`; on a pure tensor its
coefficient in degree `m` is `a` times the image of the corresponding coefficient
of `φ(b)`.

Surjectivity over a field implies that, in each degree, some original coefficient
has nonzero image: otherwise tensor induction makes that coefficient vanish
throughout the specialized image, contradicting the presence of the monomial
with coefficient one. The diagonal coalgebra image lemma then shows that a
coefficient which becomes invertible supplies that monomial in the extended
image. An additive generating set of degrees supplies all monomials by
multiplication, and linear induction gives surjectivity.

For a finite generating set, choose one coefficient with nonzero field image
per generator and multiply them. The product has nonzero image at the original
field point. Every scalar extension in which the product is invertible has all
the selected coefficients invertible and therefore has a surjective map.
`exists_away_surjective` applies this certificate to the actual principal
localization of the base ring for any finitely generated additive degree monoid.
Neither finite presentation of `B` nor noetherianness of the base is used.

The construction and proofs are internal algebraic deductions from the tensor
product universal property and the diagonal comultiplication; they do not
assume a geometric lifting assertion.
