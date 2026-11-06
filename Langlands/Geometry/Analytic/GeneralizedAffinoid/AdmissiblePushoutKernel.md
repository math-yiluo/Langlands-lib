# Exact kernels after admissible affinoid base change

This internal consequence of the actual closed-quotient and admissible-pushout constructions computes kernels for arbitrary admissible quotient maps. The imported quotient and pushout infrastructure was authored by Worker 1685; the generic kernel computation was authored by Worker 1582.

`rightKernel` constructs the actual ideal kernel of the second pushout leg, without a surjectivity assumption. `isClosed_rightKernel` proves its closedness in the stored norm topology by continuity.

`ker_rightMap_eq_of_leftEquiv` proves that transporting the first pushout algebra by an actual bounded equivalence over the base preserves the exact kernel of the second pushout leg. The two constructed transport maps carry the second legs to one another. Evaluating those two identities and using preservation of zero proves the two implications for membership in the kernels. No unproved inverse equation or flatness assumption is required.

For an arbitrary admissible map `f : A → B` and bounded `g : A → C`, `ker_rightMap` identifies the kernel of the actual base-changed map `C → B ⊗_A C` with `g.closedIdealMap (ker f)`. The original kernel is closed by continuity. The imported quotient recognition supplies a bounded equivalence from its actual presented quotient to B, over the unchanged A. Transporting the right-leg kernel through this equivalence reduces to the already proved exact kernel formula for the canonical closed quotient.

`rightKernel_eq` states the same exact computation for the constructed ideal.

Closed extension retains the actual target norm topology. All maps have their stored bounds, and the proof includes arbitrary positive radii, trivial coefficient valuations, nonreduced and zero algebras, and empty spectra. It does not assert ideal effectiveness on a finite covering or prove the special-set intersection theorem.
