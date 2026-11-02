# Fppf descent from an etale scheme atlas

Worker 421 proves
`Langlands.AlgebraicGeometry.AlgebraicSpace.etaleAtlasFppfSheaf :
EtaleAtlasFppfSheafStatement.{u}`. Worker 509 contributed the Picard
comparison route, and Worker 595 contributed the common-presentation
comparison and the dependency audit.

For every scheme `S : Scheme.{u}`, an etale sheaf on the full scheme slice
with representable diagonal and an etale geometrically surjective scheme
atlas is a sheaf for `Scheme.fppfTopology.over S`. This is the
sheaf-condition conclusion of Stacks Project Lemma 80.12.1
([Tag 076L](https://stacks.math.columbia.edu/tag/076L)), whose registered
source and conventions are documented in `EtaleAtlasFppfSheafStatement.md`.
The proof follows its quotient-presentation argument.

The atlas `a : h_U → F` has a represented kernel pair
`(t,s) : R → U` with etale projections, by the published
`exists_kernelPair`. The construction
`EtaleEquivalenceRelation.ofKernelPair` turns this into an etale
equivalence relation on the underlying schemes. Both projections commute
with the given map to `S`.

The helper `quotient_of_represented_etale_kernelPair` applies the supplied
absolute quotient statement over `S`. Its quotient has an etale
geometrically surjective presentation `b : h_U → Q`. The relation object
returned by that interface has base map `t.left ≫ U.hom`; the original
object `R` has the same base map by the slice commutativity equation.
An isomorphism that is the identity on underlying schemes transports the
quotient's represented kernel-pair square to precisely `(t,s) : R → U`.
This helper is an internal consequence of the imported relation
construction and invariance of pullbacks under isomorphism.

The final theorem supplies this helper with the independently published
unconditional theorem
`Langlands.AlgebraicGeometry.etaleEquivalenceRelationAlgebraicSpaceQuotient`,
from `EtaleEquivalenceRelationAlgebraicSpaceQuotientProof`. That theorem
constructs an actual fppf algebraic space; hence `Q.toSheaf` is an fppf
sheaf. Both `a` and `b` are locally surjective for the etale topology by
their etaleness and geometric surjectivity. The imported
`isSheaf_fppf_of_common_etale_kernelPair` compares these etale
presentations with their identical represented kernel pair and transports
the fppf sheaf property from `Q` to `F`.

The separate diagonal premise of the published statement is retained.
The proof obtains the kernel pair directly from the atlas because the
Library's `IsEtale` predicate already includes representability. All test
schemes and all sections remain in the argument at arbitrary universe `u`,
with presheaf values in `Type (u + 1)`. The theorem has no additional
hypothesis and imports no Picard statement. It supplies the generic
descent step in the field Picard comparison; it does not prove the
remaining Picard stack atlas or smooth-automorphism quotient inputs.
