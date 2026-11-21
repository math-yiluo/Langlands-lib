# Scalar symbols at the critical level

Internal proof step for Bushnell–Kutzko (1993), *The admissible dual of GL(N) via compact open subgroups*, (2.4.1)(iii), p. 65, with its proof on pp. 73–75. This is a derived, all-degree comparison, not a separate assertion quoted from those pages.

For two normalized generated fields `F[β]` and `F[γ]` on the same lattice chain, suppose `β − γ` has depth at least `d`, `k₀(β) = d`, and `k₀(γ) < d`. For the supplied tame corestriction relative to `F[γ]`, `derived_scalar_symbols` proves that its value on `β − γ` has exact depth `d` and agrees there with a scalar of `F[β]`. In each degree `j`, a scalar of `F[γ]` that lies in depth `j` also agrees modulo depth `j+1` with a scalar of `F[β]` of depth at least `j`.

The proof instantiates the two adjoint comparisons in `CriticalDerivedCentralizer` at the actual generators. The maximum characterization of the critical index gives nonvanishing by the reverse comparison. The forward comparison lets the graded scalar test of `CriticalDerivedScalars` apply both to the corestriction value and to every scalar from `F[γ]`. The result does not assert an embedding of the original fields.
