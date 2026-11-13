# Maximal open pro-p classification on available data

This internal composition works in arbitrary universe `u` on the actual rational
point topology, zero subgroup, models and quotients of a `KPBuildingDatum D`.
The only additional hypothesis is `D.SatisfiesGroupAxioms`. Availability of a KP
building assignment supplies that hypothesis for its datum.

`facetPositive_openProP` proves that every actual facet positive subgroup lies
in the zero subgroup and is open and pro-p. The inclusion and openness are the
facet-model results; the pro-p assertion applies the proved
`localFieldPositiveProP` to its actual neutral integral model and quotient.

`facetPositive_maximal_iff_isChamber` proves that this positive subgroup is
maximal among open pro-p subgroups of the zero subgroup exactly when the
original facet is a chamber. All three facet reductive comparisons are supplied
by `facetReductiveComparisons`. For the forward direction, the reduction of
the maximal positive subgroup in its own fixer is a normal Sylow subgroup.
The proved finite-field normal-Sylow criterion makes the reductive quotient a
torus, and the chamber-torus comparison identifies the original facet as a
chamber. The reverse direction uses the proved finite-field Sylow/Borel
classification, containing chambers, chamber conjugacy and the unimodular
compact-open subgroup argument through `isMaximalOpenProPIn_chamber`.

`exists_chamber_positive_eq` classifies every maximal open pro-p subgroup of
the zero subgroup as a chamber positive subgroup. It applies the existing
containing-chamber theorem with the proved comparison, Sylow/Borel and local
pro-p inputs, then maximality supplies equality. The entry definition
`maximalOpenProPRepresentative` chooses such a chamber and retains both its
chamberhood certificate and its exact subgroup equality.

`chamberMaximalProPSubgroup` sends an actual chamber to its literal positive
subgroup, certified maximal. Its value theorem is definitional equality, and
`chamberMaximalProPSubgroup_surjective` uses the representative construction
to prove that this map is onto.

These are the first three clauses of the existing corrected
`MaximalProPConclusions`. The final theorem
`maximalProPConclusions_of_chamberNormalizers` combines them with explicitly
supplied direct chamber-normalizer identities. This unit does not prove those
identities, nor claim injectivity of the chamber map or a proof of the full
`AvailableMaximalProPStatement`.

The provenance is internal composition of the actual local-model pro-p proof,
finite-field Sylow/Borel and normal-Sylow proofs, facet comparison proofs and
the chamber classification constructions. The target pair and every pair it
imports are unchanged.
