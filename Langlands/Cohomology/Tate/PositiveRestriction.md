# Ordinary cohomology comparison for positive restriction

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The comparison theorem identifies the constructed Tate restriction with
Mathlib's `groupCohomology.map` along the subgroup inclusion in every positive
degree, under the existing Tate-to-ordinary comparison isomorphisms.
The statement uses those actual maps and preserves the carrier universe.

The proof first compares both restrictions on the homology of the auxiliary
zero splice from `CochainComparison`. In degree zero the comparison follows
from invariant representatives. The embedding sequence into the actual
coinduced replacement has a surjective connecting map on positive homology
of the zero splice: its middle term vanishes in those degrees, as follows
from the already proved coinduced acyclicity and the ordinary comparison.
Naturality of the comparison connecting maps and `SplitTransfer` then
extend the equality one degree at a time. In positive degrees both splice
comparison maps are isomorphisms, so cancellation gives the advertised
ordinary restriction equality.

The conventions are from Serre, *Local Fields* (1979), Chapter VII,
section 7, printed pp. 118–119 (PDF pp. 124–125), and Chapter VIII,
sections 1–2, printed pp. 127–130 (PDF pp. 133–136). The auxiliary comparison
is an internal proof on the existing complexes; it does not replace Tate
cohomology or assume its subgroup maps.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
