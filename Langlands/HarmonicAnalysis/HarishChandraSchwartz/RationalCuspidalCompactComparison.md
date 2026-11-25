# Intrinsic cuspidality and the exact conjugation bound under compact change

This internal transport allows the analytic proof to choose a suitable
compact open Iwasawa subgroup and then serve the original arbitrary
compact choice in the VIII.3.1 target.

`rationalSchwartzCompactEquiv` is a complex linear equivalence between
the actual Schwartz spaces defined by two compact open Iwasawa
subgroups, with the same minimal parabolic and matrix height.
It uses `rationalSchwartzSubmodule_eq`, which is derived
from two-sided comparison of the actual Xi functions. Both directions
of the new equivalence keep the underlying complex function unchanged.
No topological equivalence is asserted here.

The intrinsic cuspidality membership theorem follows because every
defining translated radical integrand is unchanged. The conjugation
pairing theorem likewise keeps its exact totalized complex value,
without assuming convergence.

`rationalCuspidalConjugationConverges_of_compact` transfers the
all-conjugators integrability conclusion by applying it to the inverse
images of the two functions. Their underlying functions and intrinsic
cuspidality are identical.

`rationalCuspidalConjugationBound_of_compact` transfers the complete
local VIII.3.1 conclusion, including convergence. The bound retains
exactly the same full ambient chamber intersected with actual G¹, the
same minimal modulus, the same matrix height and the same positive
constants. Applying it in both directions gives
`rationalCuspidalConjugationBound_iff_compact`.

No connected reductivity, closedness of the matrix realization, Haar
property of the measure, Cartan covering or spectral input is required
for these transports. Constructing a compact with the additional Levi
Iwasawa and Cartan properties is not part of these transports.
This module neither constructs such a compact nor assumes that the
original arbitrary compact already has those properties.
