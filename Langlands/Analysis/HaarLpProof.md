# Haar normalization invariance of Lp membership

Author: Worker 158.

`Langlands.haarMemLpInvariant` proves the published closed proposition
`Langlands.HaarMemLpInvariantStatement` in every group universe. It compares two
Haar measures on the same Borel measurable space of a second-countable locally
compact topological group, for an arbitrary real-valued function and every
extended nonnegative exponent, including zero and infinity.

The implemented proof applies Mathlib's
`MeasureTheory.Measure.isMulLeftInvariant_eq_smul` to express the second Haar
measure as `haarScalarFactor` times the first. This factor lies in the
nonnegative reals, so its coercion to the extended nonnegative reals is finite.
`MeasureTheory.MemLp.smul_measure` then transfers membership to the second
measure. Repeating these two steps with the measures exchanged proves the
reverse implication. No division or positivity argument for the scalar is
needed. The transfer includes the measurability required by `MemLp`.

This is an internal consequence of the pinned Mathlib Haar uniqueness and
Lp measure-scaling results, imported through the published statement module.
It is a measure-theoretic prerequisite for the block-tensor comparison, not
that comparison itself. Applying it to central quotients still requires their
topological hypotheses and the transport between Borel realizations. No
representation-theoretic classification or induction result enters this proof.
