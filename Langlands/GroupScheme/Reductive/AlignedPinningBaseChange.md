# Scheme-kernel alignment under scalar extension of split pinnings

This derived internal module records the full scheme-kernel meaning of the
alignment used in the spin-cover vector-weight argument and transports it under
base change. Its provenance is the actual base-change point equivalence, the
published character-lattice equivalence for split tori, lattice-pairing
compatibility and the actual scalar extension of a supplied split pinning.

`characterLattice.TrivialOnKernel chi f` says that every point of the torus
killed by the supplied homomorphism f is killed by chi, over every relative test
scheme. It uses neither field-valued points nor a smooth or reduced kernel.
`of_postcomp` restricts the condition from a postcomposed homomorphism to f;
`comp_mono` preserves it after a monomorphic postcomposition. The proofs use
composition and cancellation, respectively.

`TrivialOnKernel.baseChange` proves this condition for the actual extended
character and homomorphism under any base map. A point of the extended kernel
corresponds, by the relative base-change point equivalence, to a point killed by
the original map on the restricted test scheme. Apply the original condition
there, use naturality of the point equivalence, and then the canonical
multiplicative-group base-change isomorphism.

`SplitPinning.FundamentalWeightTrivialOnKernel` applies the condition to every
actual torus character whose simple-coroot pairings are one at the supplied
vertex and zero at all other simple vertices. Its postcomposition lemmas are
the preceding kernel lemmas applied to the torus inclusion and the group map.
Its `baseChange` theorem treats algebraic field extensions, as required by the
published construction of actual split-pinning scalar extension. Descend an
arbitrary extended character by the split-torus equivalence; compatibility of
the integer pairing identifies the fundamental-weight conditions. Apply the
original alignment and the general scheme-kernel base-change theorem. The
simple vertex is retained by the canonical `baseChangeSimpleEquiv`.

`TitsIndexData.fundamentalWeightTrivialOnKernel_iff` identifies the host's
existing condition with this split-pinning condition on its actual pinning over
the separable closure. It is a definitional identification using functoriality
of base change. No alignment, fundamental-weight existence, character basis,
or spin-cover classification is constructed by this module.
