# Proof of smoothness invariance under an open-kernel twist

The proof was checked against the exact target and dependencies.

For a vector fixed by an open subgroup `K`, intersect `K` with the open
kernel of the character. On this intersection the scalar is one, so the
original and twisted actions agree. The intersection fixes the vector for
the other action. The Lean proof carries out this construction in both
directions of `isSmoothVector_twist_iff`, without inverse twisting or any
theorem about openness of stabilizers.

Quantifying over vectors gives `isSmooth_twist_iff`.
`twistSmoothCompatibility` packages the vectorwise and whole-representation
equivalences and closes the complete proposition without extra
hypotheses.

The coefficient ring is any commutative ring. The group has a topology, but
continuity of its group operations is not assumed. The module is arbitrary
and the three carrier universes are independent. The character's kernel is
explicitly assumed open. There is no module topology, local compactness,
unitarity, irreducibility, admissibility, or finite-dimensionality premise.

## Exact target and dependencies

- Target: `Langlands.TwistSmoothCompatibility`.
- Entry module: `Langlands.Representation.Twist.SmoothStatement`.
- Statement publication: `d6d504e524702abe3717057f4a3b879b89b61ffa`.
- Exact target fingerprint:
  `5b606583ab161aeea285dc18aaa76e10668627e0e41293c247a80b4a4ec42a9c`.
- Statement Lean SHA-256:
  `61616bd03710ca5a5c35ba3bb2b4e5793a9f15801ad99a60d7b20bd95ee3de90`.
- Statement Markdown SHA-256:
  `6e819947725e6a0877bb7d78dba6c2cbe15a6b7f273c4fe531e4ee3fdc31674e`.
- Scalar twist definition:
  `Langlands.Representation.Twist.Definitions`.
- Smoothness definitions:
  `Langlands.Representation.Smooth.Definitions`.
- Environment: Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

The statement's hashes were compared with the target: they are unchanged.
The target and both definition dependencies were confirmed public and
current, with no missing files or unavailable dependencies.

The statement's paired Markdown records the source conventions: Henniart 2000,
Section 1.2(2), printed page 440, and Casselman 2019, Chapter II, Section 1,
page 2. The implemented proof is the internal open-subgroup intersection
argument described above; it imports no other project theorem and uses no
unproved project assumption. The separate continuous-complex open-kernel
result and any smooth contragredient theorem are not dependencies here.

Native compilation and complete-target inspection succeeded, and the closing
theorem's inspected axiom closure contains only `propext` and `Quot.sound`.
