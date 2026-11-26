# Mixed adjoint bounds for the lattice layers of a simple stratum

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), (1.4.10), printed pp. 37–38 (PDF pp. 49–50), and (3.1.2)–(3.1.5), printed pp. 89–90 (PDF pp. 101–102), uses adjoint preimages to compare successive approximations. The registered source `bushnell-kutzko-1993-admissible-dual-gln` has SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

`SimpleStratum.layer` intersects the underlying lattice with the full filtration step 𝔓^k. Its Boolean argument selects the H lattice and its cutoff when true, and the J lattice and its cutoff when false. This lets the proof use the same argument for both filtrations of (3.1.7)–(3.1.10), printed pp. 90–94 (PDF pp. 102–106).

`Stratum.exists_adjoint_lift` applies `exists_commute_sub_mem` to any preimage of an endomorphism under the commutator map. Subtracting the commuting part gives a preimage at the desired filtration step with the same commutator. In `Stratum.mixedAdjointLattice_le_sup` this puts the noncentral part at the depth `k+s−t`, leaving the centralizer part at depth `k`. `mixedAdjointLattice_eq_of_sub_mem` compares two elements whose difference belongs to `𝔓^(−r)`. The difference of their commutators with an element of `𝔓^k` belongs to `𝔓^(k−r)`, which proves the equality at the approximation depth.

The critical-depth lemmas give the integer depth from the finite critical exponent and retain the level fallback for scalar elements.

For both cutoffs, `SimpleStratum.mixedAdjointLattice_le_layer` is an induction on the defining sequence. A relative preimage at `k` splits into a commuting part and a deeper part whose depth still meets the cutoff. The deeper part transfers to the next element, or lies in the full filtration summand at the terminal step. This containment proves successive high-level agreement `SimpleStratum.layer_eq_suffix` as in (3.1.9)(ii) and (3.1.10)(ii). Below the cutoff, `SimpleStratum.layer_eq_centralizer_sup` splits the layer into the relative step and the layer at the cutoff, as in the formulas after (3.1.8).
