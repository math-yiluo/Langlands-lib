# Uniqueness and functoriality of completed residue-field lifts

This is internal derived infrastructure for constructing compatible
field-valued analytic points. It uses the published actual completed residue
fields and `completedResidueComapOfEq` without altering them.

`completedResidueRingHom_ext` says that two continuous ring maps from the
completed residue field to a normed field agree if they agree on the image of
the original normed algebra. Completion induction reduces the assertion to the
normed residue fraction field. Every fraction is a quotient of images of two
original algebra elements, so the asserted agreement and preservation of
division prove equality there. Continuity and the closed equality locus extend
it to the completion. The target need not be complete.

`completedResidueBoundedAlgHom_ext` applies this uniqueness result to bounded
algebra maps. `completedResidueComapOfEq_id` and
`completedResidueComapOfEq_comp` then check the identity and composition laws
on original algebra elements, where the published evaluation formula gives
them directly. All independent algebra and field universes are retained.
These are consequences of the Library constructions, not additional claims
quoted from the literature.
