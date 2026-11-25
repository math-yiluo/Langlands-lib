# Actual anisotropic kernels of the branch-marked E6 and E7 indices

This internal module transports an actual inner type-A zero diagram to
the actual anisotropic kernel and gives its division norm-one model. Every
result is over an arbitrary field, in every characteristic and universe.
The statements about E6 and E7 retain explicit hypotheses on the entire Cartan
matrix, the exact distinguished set and triviality of the full absolute Galois
star action. They do not assert that these indices occur over local fields.

`TitsIndexData.HasInnerTypeAZeroDiagram d n` is a proposition requiring positive
`n`, an equivalence between all actual zero-restriction simple vertices and
`Fin n` preserving every ordered type-A Cartan entry, and fixation of all these
vertices by every element of the full absolute Galois group. It describes the
whole zero diagram rather than its components.

`KernelComparison.hasInnerTypeA_of_zeroDiagram` composes this numbering with
the published actual kernel vertex equivalence. The comparison preserves every
Cartan entry and intertwines each full star automorphism, so its
`star_trivial_iff` transports the full-star condition. The resulting kernel
index satisfies the existing actual `HasInnerTypeA n` predicate.

`AnisotropicKernelIndex.isSimplyConnected` applies the published theorem on
derived groups of split-torus centralizers to the actual centralizer, its
representing inclusion and its actual derived subgroup stored in the kernel
witness. It retains the ambient simply connectedness premise.

`anisotropicKernel_divisionModel_of_innerTypeAZeroDiagram` combines these facts
with `centralDivisionNormOnePresentation_of_anisotropic_innerTypeA`. The chosen
kernel is anisotropic by its published construction. Thus its actual group
scheme is isomorphic to the reduced-norm-one group of a finite-dimensional
central division algebra of reduced degree exactly `n + 1`.

The single-mark deletion lemma identifies the zero vertices with the complement
of the distinguished vertex. `finSuccAboveEquiv` numbers that complement.
Preservation of the complementary matrix gives the required type-A numbering;
the assumed full-star triviality restricts to it. For E6 and E7, deleting the
zero-based branch vertex `1` leaves, in order, vertices `0,2,3,4,...`. Direct
finite verification checks every entry of the A5 and A6 matrices respectively.
The two final theorems therefore give actual central division norm-one kernel
models of exact reduced degrees six and seven under those hypotheses.

The provenance is internal: these are transports and compositions of the
published actual kernel comparison, the split-torus centralizer derived-group
simple-connectedness theorem and the actual inner-type-A division-model
construction. No algebra anti-equivalence is produced by this module. The
relative-Weyl-to-anti-equivalence bridge, the local E6/E7 exclusions and the
full local rank-one Tits-index enumeration are not part of this module; the
exclusions are in `LocalRankOneE6Exclusion` and `LocalRankOneE7Exclusion`, and
`localRankOneTitsIndex` in `LocalRankOneTitsIndexProof` proves the enumeration
`LocalRankOneTitsIndexStatement`.
