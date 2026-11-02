# Actual reflected smaller matrices in the dominant first-block calculation

This derived algebraic infrastructure supports JPSS (1983), Section 4.9,
printed pages 416–418, and Section 4.10(2), printed page 419. It works over
an arbitrary field, with arbitrary complementary dimensions `j,k` and positive
section block sizes `a=m 0+1`, `b=m 1+1`. Write `c=j+k+1` and
`N=t+c+1=a+b+c`. The arbitrary complementary-row formulation is derived
here from the actual matrix definitions; the printed strictly dominant
illustration uses `k=0`.

`firstBlockReflectedSourceCoordinates` maps the displayed five-block order
`(a,k,1,j,b)` to the original source order `(a,b,c)` after block-Weyl
reflection. The first and second section indices reverse within their own
blocks, and the entire middle index reverses in its `c`-dimensional tail.
The private `reflectedIndex_eq_source` checks this against the published
actual ambient indices.

`blockForm_inverseTranspose_unequalRankMatrix` retains all smaller JPSS
rows. The inverse transpose of `[[v,0],[stack(z),1]]` is
`[[v^(-T),-v^(-T)*stack(z)^T],[0,1]]`. The proof constructs the inverse
block matrix, proves its product with the original matrix is the identity,
and then transposes it. The reindexed version preserves the same formula
under actual ambient rank transport.

`blockForm_firstRectangle`, `blockForm_append_firstBlockEmbedding`, and
`blockForm_dominant_blockWeyl` compute the actual matrices in the split
`a+(c+b)`. They give respectively the first padded upper rectangle,
`diag(v,1)`, and `diag(w_a,w_(c+b))`. The rectangle calculation checks all
five-by-five entries, including the separating singleton. Zero complementary
dimensions are allowed. `transpose_stackRows_left_mul` moves left matrix
multiplication through the padded row transpose by an entrywise calculation.

`firstBlock_reflection_matrix` evaluates the smaller inverse transpose at
`w_a*v^(-T)` and then multiplies by its actual smaller block-Weyl element.
It equals the actual first dominant rectangle with
`x=-w_a*v*z^T`, followed by the dominant block Weyl and the appended
first-block inclusion of `v`. Its proof applies the block formulas above,
uses involutivity of inverse transpose and its action on the Weyl matrix,
and compares the upper-right blocks through the padded transpose identity.

`firstBlockRemaining_commute` proves that the actual remaining-column
matrix `rectangularUnipotent j k (firstBlockColumns h j 0 Y)` commutes
with the appended first-block inclusion. It uses the previously computed
three-block matrices. `blockWeyl_firstBlockRemaining` identifies its
conjugate by the actual dominant block Weyl with the second dominant
rectangle whose entries are `Y i.rev l.rev`. The proof uses the published
block-Weyl entry formula, the reflected source coordinates, and the
original remaining-column block matrix. Reversing a padded tail places its
nonzero rows in the displayed `j`-block; the other two middle pieces vanish.

These are matrix equalities. This module asserts no measure transport,
reflection of slice coefficients, convergence, or global Laurent identity.
Those remain obligations of its consumers.
