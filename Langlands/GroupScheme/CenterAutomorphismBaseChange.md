# Full-centre fixation and faithfully flat base change

This internal derived module proves preservation of `AutomorphismFixesCenter`
under arbitrary change of base and reflection under flat, surjective,
quasi-compact change of base. It retains the full all-test centre functor.

Preservation uses the published equality `center_baseChange` and naturality of
the actual pullback point equivalence. For reflection, pull an arbitrary central
test point back to the cover. Its corresponding original-group point is the
restriction along the pullback projection, hence is still central. Apply the
assumed fixation upstairs, then use faithfulness of fpqc pullback to recover the
original equality. No smoothness, reducedness or representability of the centre
is assumed.

The provenance is internal composition of the existing all-test centre and fpqc
scheme descent APIs. The result applies in particular to splitting-field base
change of the actual reduced-norm-one group scheme.

`FullCenterFixationBaseChangeStatement` packages the resulting equivalence over
every pair of base schemes and `fullCenterFixationBaseChange` proves it. The
statement is an internal reusable prerequisite of the norm-one automorphism
argument, independent of reductive-group classification.
