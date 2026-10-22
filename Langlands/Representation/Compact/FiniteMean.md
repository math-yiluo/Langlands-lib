# Finite orbit means

Worker 5's algebraic construction uses normalized sums of the distinct vectors
in a finite orbit. This is internal infrastructure for Casselman's normalized
compact-subgroup projection, Chapter II, Section 1, pages 3-4, especially the
finite-coset formula in the proof of Proposition II.1.2.

The coefficient field is exactly the complex numbers. Every nonempty finite
cardinality has nonzero image in this field and hence an inverse. There is no
topology on the module.

The central counting lemma states that pulling a function back along an
equivariant map of finite sets, with nonempty source and transitive target,
preserves its normalized mean. Translation gives bijections between all fibers.
Decomposing the source into these equal-sized fibers establishes the claim.
It follows that a linear intertwiner commutes with finite orbit means.

`orbitMean` is a total auxiliary function: it uses `Nat.card` and the algebraic
`finsum`. The intended averaging properties are only asserted with finite-orbit
hypotheses. It is not an integral.

Source: `casselman-2019-smooth-representations`, SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Actual file:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
The equal-fiber proof and the use of distinct orbit vectors are an internal
algebraic implementation of that formula, not additional quoted results.

Prepared environment: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, environment artifact
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1. There are no project
mathematical dependencies in this module. Compilation is development validation;
independent acceptance has not yet been obtained.
