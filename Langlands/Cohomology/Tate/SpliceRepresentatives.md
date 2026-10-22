# Representatives at the Tate splice

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

This module uses Mathlib's actual Tate complex and its homology
objects. It identifies the existing invariant class `zeroClass` with the class
of the corresponding ordinary zero-cochain. It defines `minusOneClass` from a
vector annihilated by the actual group norm and proves that every Tate class
in degree minus one has such a representative.

For an arbitrary short exact coefficient sequence, `delta_minusOneClass`
computes the actual connecting map from degree minus one to zero: lift the
norm-zero vector to the middle coefficient module and take the norm of that
lift. If an invariant vector in the first module maps to this norm, its
degree-zero class is the connecting image. The proof uses the actual
homological connecting-map formula on representatives; there is no assumed
comparison map or boundary convention.

Source: Serre, *Local Fields*, Springer GTM 67 (1979), Chapter VIII, section 1,
printed pages 127–129 (PDF pages 133–135), for the norm-kernel and norm-quotient
presentations and the exact cohomological sequence. The explicit transport
through Mathlib's kernel/cokernel and splice isomorphisms is internal
formalization work.
