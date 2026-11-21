# Arthur–Clozel (17.7) on the actual cyclic norm-one adelic groups

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), II §17, printed pp. 197–198, derive (17.7) from
the global part of Theorem B. The identity compares the discrete sums on
the norm-one groups at the common nonnegative parameter `t` of II §9.
The base side is `G'` in Chapter II, and the upper side is the component
of the Galois generator in the Weil-restricted group.

`CyclicWeilAdelicTransport` identifies that Weil restriction with the
actual upper adelic points. Its matrix comparison is the map already
used for the factorizable tests. The transport identifies the two
norm-one subgroups and carries the component automorphism to the actual
arithmetic matrix automorphism. `CyclicTraceHaarData` starts with full
Haar measures given by the products of the local orbital-integral
measures. It specifies the norm-one Haar measures by disintegration
using the positive scalar point in both fields and the source's
split-centre Haar measures. `CyclicNormOneTraceHaarStatement` is the
existence interface for that transport and disintegration.

`CyclicDiscreteComparisonData` fixes the actual ordinary and arithmetic
spectral sums and their trace-class test domains.
`CyclicNormOneDiscreteTraceComparisonStatement` restricts an element of
the linear span of factorizable associated pairs to the two norm-one
subgroups, using inverse Weil transport on the upper test. It asserts
membership in the test domains and equality of the two discrete sums.
The degree factor is introduced by split-centre averaging in (17.8).
