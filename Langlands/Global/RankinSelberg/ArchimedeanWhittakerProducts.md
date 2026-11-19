# Paired Whittaker restrictions at the infinite places

This internal module connects the Library's real and complex Whittaker
restriction predicates to the functions on left-unipotent quotients used in
equal-rank factorization.

`realComponent_dualPoint` and `complexComponent_dualPoint` identify the
projections of `Unfolding.dualPoint`. Evaluation at a place is a ring map on
adelic entries. It preserves the long Weyl matrix because its entries are
zero or one, and it commutes with inverse transpose by the Library's matrix
map formula. Thus the projected argument is the local long Weyl matrix
times the inverse transpose of the projected point.

`IsRealPlaceWhittaker.product_unipotent_mul` and `complex_pair_invariant` take a standard adelic
additive character and two actual place restrictions, for that character
and its inverse. Each restriction is a global cuspidal Whittaker function
evaluated at the place embedding followed by a fixed adelic point. The
place embedding carries an upper unitriangular matrix to an adelic
upper unitriangular matrix. At real places this is the Library's
`realPlacePoint_mem_unipotent`. At complex places the proof checks diagonal
and below-diagonal entries in the mixed infinite coordinates and the
identity finite factor. The global left-unipotent equations multiply the
two values by reciprocal factors. The first factor has modulus one, so the
two factors cancel and the product is left-unipotent invariant.

For any field, `dual_pair_invariant` carries an invariant product to the
product of the two dual functions. Translating a local argument on the left
by an upper unitriangular matrix translates its dual argument on the left
by the conjugate of that matrix's inverse transpose by the long Weyl
matrix. This conjugate is again upper unitriangular, so the original
invariance applies. These arguments use the actual matrix and global
Whittaker covariance formulas from the imported Library modules.
