# Covariance of the adelic two-block constant term on the Levi

The two-block constant term is continuous on the adelic group and is
invariant under left translation by rational points of the embedded block
diagonal group. The calculation implements the covariance needed for the
Levi restriction in Harish-Chandra, *Automorphic forms on semisimple Lie
groups* (1968), Chapter I, §6, proof of Theorem 1, printed pp. 19–20
(PDF pp. 29–30 of the registered edition).

For rational invertible matrices $A$ and $D$ in the two diagonal blocks,
commuting $u(X)$ past $\operatorname{diag}(A,D)$ changes the upper
off-diagonal coordinate to $A^{-1}XD$. This additive coordinate change
and its inverse preserve principal matrices, so they descend to inverse
continuous maps on the matrix quotient. The descended map preserves
probability Haar measure by uniqueness. The constant term at a rational
Levi translate thus has the original integrand after a measure-preserving
change of variables, since rational left translation leaves the source
function unchanged.

For continuity, joint continuity of the integrand gives a continuous map
from the adelic group to the compact-open space of continuous functions
on the matrix quotient. That space maps continuously into $L^1$ for
probability Haar measure, and integration is continuous on $L^1$.
