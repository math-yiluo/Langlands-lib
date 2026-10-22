# Relative trace on equivariant homomorphisms

Author: Worker 45.

For ambient representations `P` and `A`, `homTransfer` sends an
`H`-equivariant map between their restrictions to the ambient equivariant
map whose value at `x` is
`sum_q q.out • f(q.out⁻¹ • x)`.

The constructor uses Mathlib's actual representation on linear
homomorphisms. Its invariant vectors are identified with equivariant maps
by `Representation.linHom.invariantsEquivRepHom`. Applying the already
constructed relative norm on these invariants produces the trace and
proves its ambient equivariance intrinsically. This avoids an equivariance
or transfer axiom.

The representative formula is proved by evaluating the coset norm.
Precomposition and postcomposition by ambient equivariant maps commute
with the trace, as follows term by term from equivariance. These are the
certificates needed to turn the standard-resolution comparison into an
ordinary cohomological corestriction chain map in `CohomologyTransfer`.

This is an internal construction from the relative norm `cosetNorm` of
`ZeroTransferDefinitions` and the
pinned Mathlib internal-Hom invariant equivalence. The relative trace
convention is that of Serre, *Local Fields*, Greenberg translation, GTM 67
(1979), Chapter VII section 7, printed pages 118–119 (PDF pages 124–125).
Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
All carriers have arbitrary common universe `u`; only the coset space is
required to have a finite enumeration.
