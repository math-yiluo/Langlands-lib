# Actual function witnesses for a corrected filtration step

Author: Worker 1312, task `277860be-2aeb-4a85-8ccb-f1e2e5c573b9`.

This internal reduction works with the published `CorrectedFiltration.step`
itself. It introduces `IsStepWitness`, a proposition about an actual function
in `term P M U h hclosed A s`. The function is supported in the upper modified
support and its image under the canonical Jacquet quotient does not belong to
the preceding image step. `step_succ_ne_iff_exists_witness` proves that such a
function exists exactly when these actual image steps differ.

A witness cannot have support in the lower group support, because its own
Jacquet class would supply a representative in the lower image. Consequently
it has a nonzero value at a point in the upper group support outside the lower
one. `cellSupport_sdiff_subset` observes that a point in a difference of cell
unions has a representative whose Weyl index belongs to the difference of the
index supports. This inclusion requires no disjointness assertion about cells.
The published `Support.modifiedRankSupport_step` says that consecutive
modified supports differ only by the whole double coset of the newly added
Weyl element. These facts yield `groupSupport_succ_sdiff_subset` and
`exists_witness_nonzero_on_doubleCoset`.

`minimal_of_step_succ_ne` is the contrapositive application of the published
`step_succ_eq`: a changing actual Jacquet step forces minimality in the whole
`W_J w W_I`, with `J = Finset.univ \\ s`. It uses the existing decreasing-length
filtration and its two-sided modified support, with no left-saturation
replacement or reversed length inequality.

The only project import is
`Langlands.Representation.Aubert.General.CorrectedFiltration`. The proofs use
its actual image definition, `mem_jacquetImage`, `step_monotone`,
`step_succ_eq`, and `Support.modifiedRankSupport_step`, together with elementary
submodule and set arguments. This is a derived construction and reduction;
it does not attribute a new theorem to an original source.

All group, root-index and representation-carrier universes retain their
independence. The input is an arbitrary smooth complex representation, with
no finite-length, admissibility, compactness, Bruhat-cover, endpoint or
compact-limit premise. These lemmas do not identify the localized grade with
a geometric intersection functor, prove support/Jacquet vanishing, or prove
`RationalCorrectedGradedVanishingStatement`. In particular, a nonzero value of
the original function alone is not asserted to give a nonzero Jacquet class;
the witness predicate retains that separate quotient condition.
