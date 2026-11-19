# Logarithmic Iwasawa coordinates on the complex matrix group

`iwasawaHomeomorph` sends an upper unipotent matrix \(u\), a real vector \(y\),
and a unitary matrix \(k\) to \(u\operatorname{diag}(\exp y_i)k\).
`quotientHomeomorph` sends the left unipotent coset of this matrix to \((y,k)\).
The projection `alphaQ` returns \(y\). Preimages under `alphaQ` of compact
sets are compact because the unitary factor is compact.

Starting with the existing factorization with a complex unit diagonal,
the proof conjugates the unipotent factor to the left, takes logarithms of
the diagonal absolute values, and absorbs the phases into the unitary factor.
The ratio of two possible unitary factors lies in the upper triangular
group with positive real diagonal. A unitary upper triangular matrix is
diagonal and its diagonal has modulus one. Positivity forces the identity.
The graph of the unique unitary factor is closed in the product with the
compact unitary group. Its description allows nonnegative real diagonal
entries, with invertibility forcing them to be positive. The logarithmic
and unipotent coordinates are then continuous by their formulas.

Left unipotent multiplication changes only the unipotent coordinate, so the
other two coordinates descend through the actual quotient. Left
multiplication by a positive diagonal translates the logarithmic coordinate
and conjugates the unipotent coordinate. These formulas supply the
transformations needed for the Weil integral.

This is an internal construction of the Iwasawa coordinates used by Jacquet
2009, §3.1, p. 11. The homeomorphisms specify the topology and coordinates
used by the ensuing measure computation.
