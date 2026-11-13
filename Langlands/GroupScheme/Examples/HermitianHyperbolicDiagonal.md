# Diagonal tori on several hyperbolic planes

This internal algebraic construction supplies the diagonal matrix part of the
split-rank lower bound. Its coordinate index consists of one endpoint family,
a remaining finite family, and a second endpoint family of the same size.
The full Gram matrix has identity cross blocks between the endpoint families
and any supplied middle matrix. No anisotropy or nonsingularity of the middle
matrix is needed for the diagonal calculation.

`diagonal` is the actual invertible diagonal matrix with entries `t`, identity,
and `t` inverse. It is a group homomorphism, is injective, has determinant one,
and commutes with coefficient ring homomorphisms. `diagonal_preserves` proves
the full Gram preservation equation whenever the coefficient involution fixes
the supplied parameters. The proof checks the nine blocks: the two identity
cross blocks use cancellation of inverse units and the middle block is fixed.
These are direct derived calculations in commutative rings and require no
characteristic restriction or classification theorem.
