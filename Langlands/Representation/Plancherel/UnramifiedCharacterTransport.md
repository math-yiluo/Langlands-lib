# Unramified characters under a multiplicative homeomorphism

Author: Worker 34.

This is an internal derivation from `unramifiedCharacters` and the
compact-open topology on continuous monoid homomorphisms in Mathlib.
It introduces no original-literature assertion.

Let `A` and `B` be groups with arbitrary topologies and let
`e : A ≃ₜ* B` be an actual multiplicative homeomorphism. Let
`ν : I → (A →* ℝ≥0ˣ)` be any indexed norm family. The three types have
independent universes. No continuity of the norms, local compactness,
Hausdorffness or topological-group hypothesis is required.

`unramifiedCharactersHomeomorph e ν` is a multiplicative homeomorphism
from the continuous characters of `A` trivial on the common norm kernel
to the continuous characters of `B` trivial on the common kernel of the
entire family `j ↦ (ν j).comp e.symm`. Both character spaces have their
inherited compact-open topology.

The forward character is precomposition with `e.symm`. A point of the
target common norm kernel has inverse image in the source common norm
kernel, so the character is trivial there. The inverse character is
precomposition with `e`; cancellation of `e.symm` with `e` verifies the
corresponding kernel condition. The two evaluation lemmas state these
formulas on every group element.

Character extensionality, subtype extensionality and inverse cancellation
prove the inverse identities. Pointwise multiplication proves
multiplicativity. Mathlib's `ContinuousMonoidHom.continuous_comp_left`
proves continuity of precomposition by either fixed continuous map;
restricting to the subtypes proves continuity on the actual unramified
character spaces. Thus the construction uses the existing compact-open
topologies and does not define either topology by transport.

This unit supplies a transport construction only. It asserts no
finite-rank parameterization, representation genericity, induced trace
equality or exact finite-length K0 comparison.
