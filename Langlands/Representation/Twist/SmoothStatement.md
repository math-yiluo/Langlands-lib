# Smoothness under a character twist with open kernel

`TwistSmoothCompatibility` states that twisting by a unit-valued homomorphism
with open kernel preserves, in both directions, smoothness of every individual
vector and smoothness of the entire representation.

The hypotheses are a commutative ring `R`, a group `G` with a topology, an
`R`-module `V`, `chi : G →* Rˣ`, `rho : Representation R G V`, and the explicit
condition `IsOpen (chi.ker : Set G)`. No topology on `R` or `V` is used.
Continuity of group operations is not needed: the proof uses only intersection
of two open subgroups. The open-kernel condition is not replaced by an
unproved implication from continuity into a topological coefficient field.

Smoothness means that each vector is fixed by some open subgroup, exactly as
in the accepted `Langlands.IsSmoothVector` and `Langlands.IsSmooth` definitions.
The original source for those definitions is Casselman, Chapter II,
Section 1, page 2, first two paragraphs; literature ID
`casselman-2019-smooth-representations`, source SHA-256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Worker 4 read that page of the retained original.
The twist convention is Henniart 2000, Section 1.2(2), page 440,
literature ID `henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
This compatibility is an internal consequence of those definitions, not a
claim that the cited pages state the generalized theorem.

Exact dependencies:

- Accepted/published smooth definitions
  `665022df-625b-44ae-9dbd-425f6e266bab`, version 1, public commit
  `10c81beaaff024987cf2945c64d0c9511f6cb686`; Lean source SHA-256
  `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`.
- Accepted/published twist definitions
  `c83db975-8b79-4fbb-9901-2db836910a0a`, version 1; Lean source SHA-256
  `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`.
  Public commit `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41` preserves these
  exact source bytes and retains the accepted smooth definitions unchanged.
- Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0,
  Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

The declaration defines a proposition and asserts no proof or axiom.
