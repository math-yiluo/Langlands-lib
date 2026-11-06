# Assembly of the actual derived-centralizer coroot comparison

Authors: Worker 1352 and Worker 1577.

This internal reduction assembles the actual geometry and integral lattice
constructions for the published
`SplitTorusCentralizerDerivedCorootComparisonStatement`. Two structural results
remain explicit premises of the final reduction:
`RootDatumExistenceStatement` and `DynamicCentralizerReductiveStatement`.
The reduction does not prove either premise or the unconditional target.

`DerivedCorootComparison P Q e` stores a base of the ambient datum `P`, a set of
root indices contained in that base's support, and the equality between the
image of the full integral `Q`-coroot span under the actual torus map `e` and
the integral span of those ambient coroots. The record retains the integral
lattice map and the selected data for downstream use. Its definition permits
any field, splitness is not part of the record, and the two root-index
universes are independent.

For a supplied compatible actual torus model `C`, the theorem
`C.exists_corootComparison` starts with actual root data `P`, `R` and `Q` for
the ambient group, its split-torus centralizer, and the supplied actual derived
subgroup, respectively. The centralizer is connected reductive. Both groups
and the derived subgroup are affine and locally of finite type. The ambient
datum `P` has a finite index type and is reduced.

The centralizer and derived torus maps are split maximal tori. The constructed
`derivedTorusCentralComplement` provides an actual central split torus whose
product with the derived torus maps flatly and surjectively onto the centralizer
torus. Actual finite Weyl-image finiteness supplies coroot uniqueness.
`IsRootDatumOf.map_corootSpan_derived` then identifies the image of the full
integral `Q`-coroot span under actual postcomposition with `C.inclusion` with
the full integral `R`-coroot span. Independently, `C.rootModel.corootFace`
provides a base of `P` and a subset of its support spanning exactly that
`R`-coroot span. Transitivity proves the displayed integral comparison.
`C.corootComparison` uses classical choice on this proved existence to
construct a `DerivedCorootComparison P Q C.inclusion`. It has precisely the
same geometric and actual-root-data inputs as `C.exists_corootComparison`.

The final reduction starts with every object and hypothesis of the unchanged
published target. It converts the split-torus centralizer to the dynamic
centralizer of a generic integral cocharacter, proves closedness of the
supplied representative, and applies the explicit dynamic-centralizer
reductivity premise to that representative. Compatible actual maximal tori
and their closed inclusion are constructed by
`splitTorusCentralizerSubgroupTorusModel`. The explicit root-datum existence
premise is applied to the ambient group, centralizer and semisimple derived
subgroup, preserving the field universe and finite reduced actual root data.
The constructed comparison record supplies the required base and subset,
together with their support inclusion and exact integral span equality.

The provenance is composition of the existing proved constructions and the
two explicitly named structural premises. There is no passage to rational
spans or saturation, replacement of the supplied centralizer or derived
subgroup, or assumption of the desired coroot-span equality. Acceptance of
this conditional reduction does not complete the unconditional proof task.
