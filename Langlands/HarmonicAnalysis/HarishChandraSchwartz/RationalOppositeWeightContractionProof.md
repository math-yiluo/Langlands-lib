# Power contraction of the actual opposite-radical weight

For a diagonal cocharacter and a vector supported on one of its weight blocks,
an opposite block-unipotent matrix preserves the vector's coordinates in that
block. The changed coordinates have strictly smaller integral weight. Conjugating
by the inverse of the m-th power of a cocharacter value with norm at most one
scales those changed coordinates by factors of norm at most the m-th power of
the unit's norm. Taking the maximum gives the bound in the diagonal basis.
The operator norms of the change of basis and its inverse transfer the bound
to the given norm.

The Iwasawa factorization expresses the action of the inverse point on the
eigenvector as the inverse eigenvalue times the action of the inverse compact
factor. Compactness bounds the norm of that latter vector from above and away
from zero. For the lower bound, applying the compact factor itself recovers
the original nonzero vector, and the compact matrix height bounds its
operator norm. The inverse eigenvalue in absolute value is the inverse square
of the Iwasawa weight when the modulus is the normalized determinant.
Comparison with the vector norm and then the square-root inequality give the
contraction estimate for the weight.

For the actual minimal weight, the eigenvector is the exterior determinant
vector of the minimal radical. Every cocharacter of the same split torus
has image in the centralizer of the generic cocharacter, so it acts on this
line. The Haar determinant formula identifies the eigenvalue's normalized
absolute value with the minimal modulus. This proves
`RationalOppositeWeightContractionStatement`, the power-bound form of
Waldspurger (2003), II.4.1 (1), printed pp. 259–260, registered as
`waldspurger-2003-plancherel`.
