# Fixed-level derivative density statement for actual cuspidal realizations

`FixedLevelDensityStatement` concerns an actual cuspidal operator realization
of `GL_(r+1)` over a number field with compact additive adelic quotient. It
takes the realization's supplied invariant positive form and a monoid
homomorphism `U` from the full adelic group to bounded complex-linear
operators on the form completion. `BoundedActionCompatibility` requires
equality on every Hilbert vector with the completed original finite action
through `AdelicGL.ofFinite` and with the completed original compact action
through `AdelicGL.ofInfinite` on the standard archimedean compact. The
proposition does not assert existence of `U` or require joint continuity
of the full action as an additional premise.

At every open finite level `J`, consider the genuine smooth vectors for
the infinite restriction in mixed archimedean coordinates whose underlying
Hilbert vectors are fixed by the finite restriction on `J`. This space uses
the subspace topology from all genuine word derivatives, including the
empty word, not just the Hilbert norm. The proposition asserts density of
the subset whose underlying vectors are canonical images of original
vectors fixed at the same level. It retains the number field universe as a
free parameter. The assertion is an internal consequence of compact-finite
smooth density, the fixed-level derivative equivalence, and actual cuspidal
joint vector recovery.

The helper `dense_fixedSmoothImage_of_jointRecovery` combines the standard
compact density theorem, the supplied action comparisons, and fixed-level
joint recovery for an arbitrary compatible form completion. The cuspidal
proof supplies joint recovery using admissibility.
