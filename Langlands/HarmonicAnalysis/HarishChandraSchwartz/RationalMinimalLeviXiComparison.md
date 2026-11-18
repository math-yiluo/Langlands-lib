# The Xi comparison on the full minimal-Levi chamber

This internal adapter derives the lower estimate for the actual standard-Levi
Xi on every point of the full minimal-Levi closed chamber. The lower estimate
requires only the supplied structural basis and empty-index Levi Cartan
covering, and the original group, compact and Iwasawa data. It assumes no upper
Xi estimate.

The proof first transfers the original simultaneous standard basis to the
canonical Levi scheme using Worker 658 and Worker 734's unchanged inheritance
modules. Its minimal-face basis contains a member inside the original
Iwasawa compact's Levi preimage, so the published intrinsic lower Xi estimate
applies to a compatible component. Every ambient dominant cocharacter is
dominant for the intrinsic Levi, since its simple roots are exactly the
selected ambient simple roots. The canonical point equivalence and modulus
comparison identify the intrinsic estimate with the actual standard-Levi Xi
and its minimal half modulus.

A generic compact-extension lemma extends a lower Iwasawa-weight estimate
under compact left multiplication in the parabolic. The Iwasawa half-weight
is bounded on the compact multiplier set, and reverse Xi translations are
uniform on its inverse set. The full minimal-Levi compact dominant reduction
and centrality of uniformizer points then give the lower estimate on every
original chamber point.

Combining it with the preceding full-minimal-Levi upper extension and the
exact modulus factorization proves `HasRationalXiLeviComparison` from the
separately owned `RationalXiUpperBoundStatement`. That substantive upper proof
remains an explicit input and is not supplied here.
