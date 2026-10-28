# Surjectivity of restriction to a closed subset

This proof module establishes
`Langlands.HarmonicAnalysis.SchwartzBruhat.closedRestrictionSurjective.{u}`
of exactly the published proposition
`Langlands.HarmonicAnalysis.SchwartzBruhat.ClosedRestrictionSurjectiveStatement.{u}`.
It uses the actual complex linear map `SchwartzBruhat.restrictClosed` and the
existing `SchwartzBruhat` spaces, with the induced topology on the closed
subset. It reuses the compact-clopen neighborhood lemma
`Langlands.HarmonicAnalysis.exists_compact_clopen` from
[RowTensorDecompositionProof](../RowTensorDecompositionProof.md). That existing
helper is now public with its statement and proof unchanged; the duplicate
private helper has been removed from this module.

The proof is an internal topological argument. For a Hausdorff, locally compact,
totally disconnected space, Mathlib's
`loc_compact_Haus_tot_disc_of_zero_dim` supplies a clopen neighborhood basis.
Intersecting a prescribed neighborhood with a compact neighborhood and choosing
a clopen basis element inside their intersection gives a compact clopen
neighborhood. A finite subcover then places any compact set inside a compact
clopen subset of a prescribed open neighborhood.

Consequently, if `K` is compact and open in a subspace `Z`, choose an ambient
open set whose trace is `K`. The image of `K` in the ambient space is compact,
so the preceding construction supplies a compact clopen set `U` containing
that image and contained in the chosen open set. The trace of `U` on `Z` is
exactly `K`.

For a Schwartz–Bruhat function `f` on `Z`, the existing finite-range lemma
`finite_range_of_locallyConstant_of_hasCompactSupport` shows that there are
finitely many nonzero values. Each corresponding fiber is compact by
`Hecke.TestFunction.isCompact_fiber` and open by local constancy. Choose a
compact clopen ambient lift for each such fiber and sum its characteristic
function weighted by the fiber's value. Each characteristic function belongs
to the actual ambient Schwartz–Bruhat space; the finite sum therefore does
too. At any point of `Z` with nonzero value, exactly its own fiber contributes;
at a zero of `f`, no summand contributes. The evaluation law
`restrictClosed_apply` proves that the sum restricts to `f`. The ambient lifts
may overlap away from `Z`, which does not affect this calculation.

The theorem quantifies over the original arbitrary universe, topology,
Hausdorffness, local compactness, total disconnectedness, closed subset and
closedness proof. It assumes no countability, group, manifold, measure,
compactness of the entire space or nonemptiness. The empty family of nonzero
fibers gives the zero extension, including empty spaces and subsets.
Closedness is used by the published restriction map to preserve compact
support; the compact-open trace lemma itself works for any subspace.

The published statement explains its motivation from Shalika (1974),
Lemma 1.15, printed page 178 (PDF page 9), registered as
`shalika-1974-multiplicity-one`. This proof proves the stated generalization
by compact-open fibers rather than by the source's coordinate localization.
It asserts no distribution descent, orbit vanishing or multiplicity-one
result.
