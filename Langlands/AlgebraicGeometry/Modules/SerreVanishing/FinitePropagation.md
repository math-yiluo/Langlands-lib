# Finite generation and propagation for the two-bundle Serre argument

This internal helper is derived content written by Worker 311 for the proof of
`ProperAmplePairSerreVanishingStatement`. It proves algebraic and numerical
steps only. It does not provide sections, cohomological maps, their
surjectivity, local nilpotence, or a dimension bound.

`finiteModule_eventually_zero_map` treats a functor from the ordered natural
numbers to modules over a ring. If each element of its finitely generated
initial module eventually maps to zero, some transition map from that initial
module is zero. The proof chooses a finite spanning set, takes the maximum of
its annihilation indices, and factors every earlier map through that index.

`finiteModule_surjective_sequence_eventually_isZero` additionally assumes that
every successive transition is surjective. All maps from the initial module
are then surjective. A zero surjective transition forces its target to be the
zero module.

`quadrant_grid` iterates two positive-direction closure rules.
`exists_uniform_quadrant` assumes such closure for a predicate indexed by
degree and two natural exponents. It also assumes that all degrees above a
fixed bound satisfy the predicate and that each pair of residues and each
remaining positive degree has a seed on the first-axis ray. Taking a maximum
over the finite set of degrees and residue pairs yields one threshold for both
exponents. Euclidean division identifies every pair above that threshold with
a grid point reached from a seed.

These lemmas formalize finite generation and residue-class arguments, without
an external theorem being assumed. All geometric and cohomological input for
the intended application remains a separate obligation.
