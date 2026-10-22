# Proof of finite-relative Hilbert 90

Worker 80's proof applies Mathlib's `H1_induction_on` to the
actual cohomology of `unitsRepresentation`. A representative additive
cocycle becomes a multiplicative unit-valued cocycle by `Additive.toMul`.
The action is unchanged by restriction to the lifted integer scalars, so
the cocycle identity is the same identity.

Mathlib's universe-polymorphic
`isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` supplies a unit whose
coboundary is the representative. The same unit in additive notation
therefore witnesses membership in the actual low-degree coboundary range.
Explicitly, the witness satisfies `g(β) / β = f(g)`; this is the
additive differential `g • Additive.ofMul β - Additive.ofMul β`.
`H1π_eq_zero_iff` shows that the class is zero. Equality of every class to
zero gives the required subsingleton.

The theorem's exact type is `FiniteRelativeH1Vanishing.{u,v}`, imported
from the published `RelativeH1Statement` module. The base and extension
universes remain independent. This result supplies the finite-relative
H¹ clause of `CohomologyExistence`; the absolute H¹ and H² clauses require
separate arguments.

The original Hilbert 90 proof is Serre, *Local Fields* (English translation,
1979), Chapter X, section 1, Proposition 2, p.150 / PDF156. Source ID
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
The paired statement explains the derived extension to finite
non-Galois extensions. The implemented route reuses the existing Mathlib
proof of the elementary automorphism cocycle theorem, rather than its
Type-0-only bundled cohomology instance.

Worker 66 checked the supplied proof against the published target and
coefficient definitions, read the cited original passage, and prepared
this submission. The Lean proof is unchanged from Worker 80's draft.
The Mathlib revision used here is
`5ed2965256430c3649e86755f9576b54eca72435`.
