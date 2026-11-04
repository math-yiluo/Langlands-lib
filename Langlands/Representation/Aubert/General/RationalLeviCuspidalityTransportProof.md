# Proof of actual standard-Levi cuspidality transport

Author: Worker 189. This proves exactly `Langlands.Aubert.General.RationalPointFamily.RationalLeviCuspidalityTransportStatement` at independent field and representation universes.

The proof specializes `standardLeviStandardFamilies` to the published actual representative `Standard.leviScheme`. Its intrinsic simple roots are exactly the selected ambient character subset. `leviSimpleRootEquivOfEq` therefore identifies an intrinsic simple root with its literal ambient root in `I`, preserving the underlying character. `properFinsetEquiv` lifts this equivalence to all proper finite subsets. The root-set lemma proves that mapping a finite intrinsic subset through this equivalence and `leviIndex` leaves its exact character subset unchanged.

For each such subset, the standard-family comparison supplies equalities between the intrinsic Levi and unipotent subgroup functors and inverse images of their ambient counterparts. Evaluating these equalities at the identity test scheme gives the subgroup membership equivalences required for cuspidality transport. The forward map of `leviRationalPointHomeomorph` is precisely the rational-point map of the canonical Levi inclusion, so these membership equivalences refer to the actual canonical homeomorphism and the literal inside-Levi subgroups.

Finally `isCuspidalFor_pullback_iff` transports vanishing of all normalized Jacquet modules through that homeomorphism and the bijection of proper subsets. It applies to the arbitrary legal decompositions and closedness proofs in the statement. Both point groups retain their canonical evaluation topologies, and the literal subgroup retains its inherited topology.

The argument is an internal consequence of the published standard-family comparison and normalized Jacquet transport. The dynamic Lie and standard-cocharacter assumptions, connected reductivity of the actual Levi, and stated topology, decomposition and closedness inputs remain explicit. Empty root systems and subsets are included. The proof establishes no structural antecedent, compact-coefficient result, norm-kernel restriction theorem or final Howe implication.
