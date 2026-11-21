# Fixed-level derivative density statement for actual cuspidal realizations

`FixedLevelDensityStatement` concerns an actual cuspidal operator realization
over a number field with compact additive adelic quotient, a supplied
invariant positive form, and a full bounded adelic representation on its
Hilbert completion. The finite and compact actions of this representation
agree with the completed original actions.

At every open finite level, consider the infinite-action smooth vectors
whose underlying Hilbert vectors are fixed at that level. This space uses
the subspace topology from all genuine word derivatives. The proposition
asserts density of the subset whose underlying vectors are canonical
images of original vectors fixed at the same level. It retains the number
field universe as a free parameter. The construction is an internal
specialization of the original fixed smooth image of a Hilbert completion.

The helper `dense_fixedSmoothImage_of_jointRecovery` combines the standard
compact density theorem, the supplied action comparisons, and fixed-level
joint recovery for an arbitrary compatible form completion. The cuspidal
proof supplies joint recovery using admissibility.
