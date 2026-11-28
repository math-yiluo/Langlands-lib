# Cuspidal kernel vectors for Levi fibre pairings

The norm-one partial convolution of a quotient \(L^2\) class is an inner
product against a kernel vector. Orthogonal projection of the vector into the
closed cuspidal subspace preserves its inner product with each cuspidal class.
The projected vectors are rationally invariant by uniqueness in the Hilbert
space. Their positive coordinates lie in the projection of the test kernel's
support because the convolution variable belongs to the norm-one subgroup.

The uniform rapid-decay estimate for a partial convolution bounds the norm of
its projected kernel vector. Evaluate the estimate against the vector itself,
use its squared norm as the inner product, and cancel its norm when it is
positive. This anticipates the integrability of the fibre pairings of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, §6.2,
(6.8).

For a fixed kernel \(K\), a continuous rationally invariant function \(f\), and
a continuous scalar weight \(d\) on the positive subgroup, `cuspidalFibreVector`
integrates these vectors over the positive subgroup times the norm-one
rational quotient. At \(b\) the integrand at \((t,[y])\) is the projected
kernel vector at \(y\,p(t)\), multiplied by \(d(t) f(y\,p(b)p(t))\), where \(p\)
is the positive point map. The two factors are jointly continuous in \(t,y\)
and rationally invariant in \(y\), so the product descends continuously to the
quotient. Pairing the Bochner integral with a cuspidal vector commutes with
integration whenever the vector integrand is integrable. The resulting
iterated scalar integral uses the conjugate of the partial convolution,
since the integrated vector is in the second slot of the inner product.

Under the rapid-decay statement and the test-function hypothesis on \(K\),
polynomial growth of \(f\) gives a norm majorant for the vector integrand.
Choose the rational representative supplied by the decay estimate at the
growth exponent of \(f\). The submultiplicative height bound for \(f\) then
cancels the inverse height factor for the vector. The remaining factors in
\(t\) are bounded on the compact positive image of the support of \(K\), and
the vector vanishes elsewhere. Finite norm-one quotient volume makes the
compact-support majorant integrable. The majorant is locally uniform in \(b\),
so dominated convergence gives norm continuity. Integration of the same
majorant gives the growth bound in \(p(b)\) with the exponent of \(f\).
