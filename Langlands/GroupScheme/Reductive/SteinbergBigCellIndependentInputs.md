# The unchanged Steinberg target from explicit structural inputs

This internal reduction proves that five explicit structural propositions
imply the unchanged `Langlands.GroupScheme.SteinbergBigCellStatement.{u}`.
The record `IndependentSteinbergInputs` contains actual root-datum existence,
rank-one root cells, root Lie lines, integral coroot generation for simply
connected groups, and opposite factor pairs over algebraically closed fields.
Its name does not certify any proof of those propositions. The reduction
asserts none of their existence proofs, and gives the
unconditional target only together with proofs of those inputs.

For an algebraically closed field `k : Type u` of positive prime
characteristic `q` and an actual simply connected group `G`, the generic
maximal-torus existence and separably closed splitting theorems choose an
actual split maximal torus. The explicit pinning constructor consumes the
supplied root-datum proposition and the supplied line witnesses, rather
than an unconditional root-line theorem. Integral coroot generation is a
separate supplied proposition. The new structural-statement reduction
constructs full linked root maps for all roots of this pinning and hence
its full simple-root family, from the supplied cell and line statements.

The opposite-pair covering adapter supplies the actual Bruhat covering of
the polarized-rho dynamic subgroup. It does not identify that subgroup as
Borel. The supplied-family seven-law constructor then gives the actual
witness bundle, including its cofinal whole-space irreducibility law, with
all relative scheme tests retained. The bundle's forgetful theorem yields
exactly the original existential statement. No representation-existence or
irreducibility proposition is added to the input record.

The implemented maximal-torus route bounds torus ranks by the ambient Lie
dimension, chooses a maximal rank, and splits a torus over a separably
closed field. The pinning, full-root-family, covering and representation
steps all retain their structural inputs explicitly. The old unconditional
Steinberg/Borel assembly, canonical linked-root choice and root-line/root-cell
proofs are not used. This is derived internal assembly of Library algebra and
the supplied-data support; it adds no new external source assertion.

The structural existence proofs are separate:
`steinbergBigCellIndependent` (module
`Reductive.SteinbergBigCellIndependentProof`) proves all five inputs from the
rank-one central cover and applies this reduction. This conditional reduction
is not by itself a proof of any of these premises.
