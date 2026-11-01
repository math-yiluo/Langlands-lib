# Fixed gamma factors on the actual lower real ray

This internal module fixes the two block gamma factors in the actual
large-second-twist theorem, conditional on the explicitly supplied proposition
`UnramifiedTwistGammaStatement`. It does not prove unramified gamma transport.

The first helper specializes that transport proposition to the canonical
determinant-power character, using the canonical normalized absolute value.
The main theorem chooses complete gamma certificates for the fixed equal-rank
block and the fixed rank-one block from their full Whittaker types. Complete
certificate uniqueness identifies the first factor in every large-twist
certificate with the chosen fixed factor. Unramified transport and uniqueness
identify the second factor with the spectral rescaling of the chosen rank-one
factor. Complete-certificate commutation and the actual lower-family
representation equivalence then give certificates for the literal second-block
deformation on one real ray.

Both original representation carriers and their independent universes are
retained. No irreducibility or coefficient-realization premise is added.
The real-ray predicate records complete gamma certificates, rather than only
functional equations for selected tests. This is a derived composition of the
existing construction, large-twist, equivalence, and uniqueness results.
