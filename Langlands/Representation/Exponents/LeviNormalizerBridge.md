# Split components and normalizers of represented centralizers

This internal construction extends the actual split-component restriction
in `SplitComponentNormRigidity` to an automorphism. Its inverse is the
restriction of the inverse ambient automorphism; both inverse identities
follow by cancellation of the closed split-component embedding.

The normalizing equation for a representative then implies the normalizing
equation for its split component.

If a representative is the all-test dynamic centralizer of a cocharacter,
that cocharacter factors through its split component. This gives containment
of the whole split-component centralizer in the representative. Centrality
of the split component gives the reverse containment on every test scheme.

For an actual rational Levi, the current corollary retains the explicit
`ParabolicDynamicStatement` input. The geometric unipotent-radical input is
discharged using its published proof. No closed rational-parabolic
classification theorem is asserted.

For a connected reductive representative over a nonarchimedean local field,
preservation of all rational-character norms on central rational points
fixes its split component by `comp_automorphism_eq_of_norm`. A normalizer
therefore belongs to the representative whenever the all-test centralizer
equality is supplied.

These are derived structural helpers for the normalizer inputs in the proof
of Renard VI.8.5; they do not prove generic irreducibility.
