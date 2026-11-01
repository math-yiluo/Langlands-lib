# Joint convergence on an adjacent-rank determinant shell

This derived helper concerns JPSS (1983), Section 6.3, printed
pages 433–436, formulas (5) and (11). Its kernel on the actual quotient
times the actual general linear group is

`1_(ord(det g)+ord(det h)=m) W(g) W'(g h) phi(lastRow g) Phi(h) a(h)`.

Here `W` is an actual coefficient-image vector of an arbitrary smooth
representation in independent universe `uV`, `W'` is an inverse-character
Whittaker function, `phi` is a row Schwartz–Bruhat test, `Phi` is a square
matrix Schwartz–Bruhat test, and `a` is any scalar multiplier. Every
canonical p-adic field, every supplied unitary additive character, zero
vectors and tests, and actual inner rank one are included.

The standard and inverse characters cancel, so the kernel descends in
`g`. If `W'` and `a` are continuous, the kernel is jointly continuous.
The shell is clopen, and continuity of the shifted pairing follows
through the product of the open quotient map with the identity.

The proof of compact support uses the published smooth simple-root
support and Whittaker row-slice compactness theorems, rather than an
asymptotic growth estimate. Smooth Whittaker row data and the matrix test
each give a lower bound on their determinant orders at every nonzero
point. For the row data this follows from smooth simple-root support
and the Schwartz–Bruhat row bound; for the square matrix test it follows
from bounded determinant norm on its compact support. In both cases
unbounded powers of the residue cardinality convert a determinant-norm
upper bound to a determinant-order lower bound. Fixing the sum of those orders bounds each order above as well.
Only finitely many individual determinant slices can occur. On each
one, Whittaker row data has compact support in the quotient and the
matrix test has compact support on the general linear group. The joint
support lies in the product of the two finite unions of compact sets.

The compact-support conclusion requires no regularity or growth bound
on `W'` or `a`. Their continuity gives absolute integrability for the
product of any two supplied Borel measures finite on compact sets.
This includes the shared group Haar measure and compatible quotient
measures once those measure properties are installed. No integrability
is assumed as a substitute for this conclusion.

This is a derived formal route to the fixed-shell convergence used in
the source. The source is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 432–436 were visually read, and 433, 435 and 436 reread
during this implementation. The source proves a stronger weighted
series convergence using torus gauges. This helper proves only
fixed-shell convergence. Global series convergence, the initial model
substitution, quotient shear, Laurent convolution, functional equations,
and both parent gamma/L statements remain separate obligations.
