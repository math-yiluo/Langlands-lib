# Naturality of ordinary cohomological transfer

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The standard-resolution cochain coordinates commute with coefficient maps:
the free-module universal property proves this before precomposition with
Mathlib's bar-to-standard isomorphism. Relative trace commutes with
postcomposition, so the actual ordinary cochain transfer is natural in
coefficients. Applying homology gives ordinary transfer naturality in every
natural degree.

The cochain transfer extends from the restricted auxiliary zero splice to
the actual Tate complex, with zero components in negative degrees. Its
positive homology is precisely the independently constructed ordinary
transfer, conjugated by the existing comparisons. Coefficient naturality
then gives a map of short exact sequences of complexes; naturality of the
actual connecting morphisms proves its boundary compatibility.

These are internal comparison lemmas toward `OrdinaryComparisons`, with
Serre's transfer conventions from *Local Fields* (1979), VII section 7,
printed pages 118–119, and VIII section 2, printed pages 129–130.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The degree-zero formula is established in `CohomologyTransferZero`;
`PositiveCorestriction` uses it to identify this comparison with the
recursively defined Tate corestriction. All carriers retain the arbitrary
common universe `u`. Cochain naturality requires only finite coset space;
the map to the Tate complex additionally uses finiteness of the ambient group.
