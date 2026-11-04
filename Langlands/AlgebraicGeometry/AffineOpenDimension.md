# Dimension on opens of finite-type spectra

This is a derived prerequisite for the chart arguments supporting the
pure-dimensional fibre clause in Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed pp. 5–6,
Theorem 3.4(2). Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
These open-subspace dimension comparisons are internal prerequisites,
not separately numbered assertions of the source.

`localizationAwayBasicOpenHomeomorph s` constructs the homeomorphism
from the actual spectrum of the localization of A away from s to the
basic open D(s) in Spec A. It is induced by the localization structure
map and its known open embedding and range. This construction applies
to every commutative ring and every element, including zero.

For a finite-type domain A over an arbitrary field k and nonzero s,
`topologicalKrullDim_basicOpen_of_finiteType_domain` identifies the
dimension of D(s) with the Krull dimension of A. The proof transports
dimension through this homeomorphism and applies the principal
localization dimension comparison from `FiniteTypeDomainDimension`.

`topologicalKrullDim_open_of_finiteType_domain` proves the same equality
for every nonempty open U in Spec A. Choose a point in U and a basic
open D(s) containing it and contained in U. The element s is nonzero.
Subspace dimension monotonicity bounds the dimension of U between
that of D(s) and that of Spec A; both equal the dimension of A.

For any prime ideal p in a finite-type k-algebra A,
`topologicalKrullDim_open_primeZeroLocus` proves that every nonempty
open of V(p), with its subspace topology, has dimension equal to the
Krull dimension of A/p. The proof pulls the open back through the
actual quotient-spectrum homeomorphism, applies the preceding domain
result to A/p, and transports back. The algebra A itself need not be
a domain or reduced. The field and algebra occupy independent universes.

These comparisons do not assert pure-dimension locality for arbitrary
schemes, scalar-extension invariance, constructibility, or filtered
descent. Nonemptiness of the chosen open and finite type over the
field are retained wherever required for dimension equality.
