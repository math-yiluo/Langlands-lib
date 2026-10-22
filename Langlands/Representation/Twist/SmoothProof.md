# Proof of smoothness invariance under an open-kernel twist

Worker 4 authored the complete Lean proof. Worker 14 checked the shared proof
against the exact accepted target and dependencies and prepared this contribution.
Both workers are recorded as coauthors. Native compilation is development
evidence; independent proof acceptance is recorded by the checker and review receipts.

For a vector fixed by an open subgroup `K`, intersect `K` with the open
kernel of the character. On this intersection the scalar is one, so the
original and twisted actions agree. The intersection fixes the vector for
the other action. The Lean proof carries out this construction in both
directions of `isSmoothVector_twist_iff`, without inverse twisting or any
theorem about openness of stabilizers.

Quantifying over vectors gives `isSmooth_twist_iff`.
`twistSmoothCompatibility` packages the vectorwise and whole-representation
equivalences and closes the complete accepted proposition without extra
hypotheses.

The coefficient ring is any commutative ring. The group has a topology, but
continuity of its group operations is not assumed. The module is arbitrary
and the three carrier universes are independent. The character's kernel is
explicitly assumed open. There is no module topology, local compactness,
unitarity, irreducibility, admissibility, or finite-dimensionality premise.

## Exact accepted target and dependencies

- Target: `Langlands.TwistSmoothCompatibility`, artifact
  `f3828b8f-ac55-4352-955b-9dc9787da742`, version 1.
- Entry module: `Langlands.Representation.Twist.SmoothStatement`.
- Statement publication: `d6d504e524702abe3717057f4a3b879b89b61ffa`.
- Independent statement publication receipt:
  `5e5bb79f-ad67-4eaa-98e1-43127aa1e000`.
- Exact target fingerprint:
  `5b606583ab161aeea285dc18aaa76e10668627e0e41293c247a80b4a4ec42a9c`.
- Statement Lean SHA-256:
  `61616bd03710ca5a5c35ba3bb2b4e5793a9f15801ad99a60d7b20bd95ee3de90`.
- Statement Markdown SHA-256:
  `6e819947725e6a0877bb7d78dba6c2cbe15a6b7f273c4fe531e4ee3fdc31674e`.
- Scalar twist definition:
  `c83db975-8b79-4fbb-9901-2db836910a0a`, version 1,
  `Langlands.Representation.Twist.Definitions`.
- Smoothness definitions:
  `665022df-625b-44ae-9dbd-425f6e266bab`, version 1,
  `Langlands.Representation.Smooth.Definitions`.
- Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
  Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

The full final statement review was read and its effective hashes were compared
with the shared target: they are unchanged. Fresh registry fetches at submission
confirmed the target and both version-1 definition dependencies are accepted,
public, and current, with no missing files or unavailable dependencies.

The statement's paired Markdown records the source conventions: Henniart 2000,
Section 1.2(2), printed page 440, and Casselman 2019, Chapter II, Section 1,
page 2. The implemented proof is the internal open-subgroup intersection
argument described above; it imports no other project theorem and uses no
unproved project assumption. The separate continuous-complex open-kernel
result and any smooth contragredient theorem are not dependencies here.

Native compilation and complete-target inspection succeeded, and the closing
theorem's inspected axiom closure contains only `propext` and `Quot.sound`.
These development checks do not replace the registered independent checker
or independent semantic review.
