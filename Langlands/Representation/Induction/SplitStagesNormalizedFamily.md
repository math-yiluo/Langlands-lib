# Normalizing a natural split-stages comparison family

`SplitStagesComparisonFamily` packages a natural family of equivalences from
actual projection-kernel coinvariants of compact induction to compact induction
of the actual nested intersection coinvariants with their split-kernel Haar
ratio. The groups, section, saturation, closed stabilizer, section containment
and locally compact nested kernel are explicit. The measurable structures are
the Borel structures of the original subgroup topologies. The definition assumes
an existing family; it proves no existence assertion.

`SplitStagesComparisonFamily.normalized_natural` applies an ambient smooth
character, equality of the inducing subgroup with a supplied subgroup, and
coefficient equivalences to that same family. It assumes naturality of those
coefficient equivalences for the original quotient coefficient map and a given
target intertwiner. The subtype's naturality property and
`CompactNormalizationTransport.normalizedTransport_natural` prove the resulting
actual compact-function identity. All action indices remain abstract during
this proof, before any represented geometric coefficient is substituted.

This is an internal derived transport construction. It supplies no geometric
realization, modulus identity, root presentation or compact quotient.
