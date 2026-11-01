# Joint continuity of the actual adelic section action

Author: Worker 2. Provenance: internal construction from the actual adelic
matrix-group topology and the dedicated compact-open section spaces.
No new original-literature identification is made.

The number field and complex normed coefficient spaces have independent
universes. Every natural matrix rank and ordered positive block shape is
retained. The sections remain the actual parabolic-covariant functions with
a common open finite stabilizer and real-smooth archimedean slices. Their
topology is exactly the previously constructed compact-open topology induced
by their faithful continuous-function realization.

`toContinuousMap_rightAction_eq` identifies the existing section action
with actual right translation on continuous functions. The actual full
adelic matrix group is locally compact by the imported construction.
Consequently its compact-open right-translation map is jointly continuous.
Composing this map with the continuous section realization and using the
induced target topology proves `continuous_rightAction_joint`: both the
group element and the section vary. The induced topology also transfers
continuity of each continuous-function orbit to the full adelic section
orbit map. The same realization and joint evaluation
on the locally compact group prove `continuous_evaluation`.

`rightContRepresentation` bundles the existing right action as a monoid
homomorphism into continuous complex linear operators. Its identity and
composition laws are exactly those of the existing section representation.
Its underlying algebraic representation equals `rightAction`.
Mathlib's `ContRepresentation` alone expresses continuity of each linear
operator; the separately proved joint continuity theorem supplies the
stronger assertion for this constructed action.

For an actual Levi coefficient intertwiner with proved continuity,
`contIntertwiningMap` bundles the existing continuous coefficient
postcomposition map as a continuous intertwiner between these actual
representations. Its evaluation agrees with `mapCLM`, and its intertwining
identity is the established coefficient-map equivariance.

No completeness, finite dimension or continuity of the supplied Levi
representation is assumed. This topology controls function values on
compact sets. This unit makes no assertion about derivative topologies,
smooth orbit maps, nonzero sections, Haar normalization, unitary completion
or automorphic existence.
