# Unequal-rank character-change block geometry

This is internal derived content from the published Whittaker character-change
diagonal and the actual JPSS block matrices in `QuotientIntegrals`.

For small rank n+1, gap d=j+k+1, and large rank n+d+1, let D be the
large diagonal diag(a^(n+d),...,1). The fixed right correction R has leading
block a^d I_(n+1), and thereafter the corresponding entries of D. The rectangular
linear equivalence S multiplies row i (numbered from zero) by a^(-(i+1)); its
inverse multiplies that row by a^(i+1).

The implemented identity is D M(g,x) = M(d_a g,Sx) R. Its proof compares matrix
entries in the leading block, the rectangular block, and the remaining identity
block. Natural exponent subtraction is justified by the index bounds, and
cancellation takes place among actual field units. Empty rectangular blocks and
rank-one leading blocks are included.

This unit supplies algebraic block geometry. It does not establish a Haar
Jacobian, convergence, rational continuation, or a local-factor comparison.
