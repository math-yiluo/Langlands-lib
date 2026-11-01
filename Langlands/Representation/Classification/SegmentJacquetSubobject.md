# Centrally separated cuspidal Jacquet subobjects of segments

This internal helper treats every actual irreducible subrepresentation of an
increasing segment induction. Its full cuspidal normalized upper Jacquet module
is quasicuspidal and has an actual simple series on which one central block
scalar acts through pairwise distinct scalars.

`exists_subrepresentationJacquetSeries` proves existence of that series.
`IsSegmentSubrepresentation.cuspidalJacquetSeries` chooses the actual series
and scalar function, retaining the simple-factor, injectivity and actual
scalar-action proofs in its type. The central element is the published
`SegmentFullJacquet.separatingScalar`; its commutativity with every element
of the uniform product Levi is the published `separatingScalar_comm`.
`subrepresentationJacquet_isLeviQuasicuspidal` proves actual vanishing of
every proper refined unipotent coinvariant quotient.

The relations are the weak actual segment subrepresentation relations.
Strong segment socles satisfy them through the published implication.
All primes, supplied p-adic fields and compatible topological data are
preserved. Field and original carrier universes remain independent, with
the induced and Jacquet carriers in `Type (max uF uV)`.

Fix an actual supercuspidal representative of the segment base. Its
admissibility and irreducibility give a scalar central character by the
published admissible Schur theorem. The actual associated-Jacquet filtration
of the full increasing induction, together with the published
`exists_segmentJacquetFiltration`, has simple Weyl-transport factors.
The separating scalar acts on them through `segmentScalar` of the block
permutation. The published injectivity of `segmentScalar`, of `blockPerm`,
and of the filtration's enumeration makes these scalars pairwise distinct.

The supplied constituent embeds into that increasing induction. Actual
smooth coinvariant exactness makes its normalized upper Jacquet map
injective. The Jacquet input has finite length by irreducibility, and
published normalized Jacquet finite-length preservation gives finite length
of the output. The generic
`SmoothRep.exists_scalarSeparatedSeries_of_injective` then extracts a
simple series with an injective subfamily of the ambient scalars.

For quasicuspidality, the published unconditional associated-Jacquet
filtration theorem also asserts quasicuspidality of the full Jacquet module
of this cuspidal induction. The actual injective map presents the
constituent's Jacquet module as a smooth subquotient. Published
`leviQuasicuspidalSubquotient` gives the stated vanishing.

The substantial inputs are the generic scalar-separated subobject theorem,
`Classification.SegmentFullJacquetSplitting` and its scalar-computation
imports, the unconditional `CuspidalSupport.AssociatedProof`, actual
smooth coinvariant exactness and unipotent finite containment,
`CuspidalSupport.QuasicuspidalSubquotientProof`, normalized finite-length
preservation, and admissible Schur theory. This is an internal combination
of the supplied generic extraction module and those published mathematical
results, without a new literature transcription.

The result does not identify this entire Jacquet module with the increasing
tensor. It needs no adjacent two-supercuspidal formula, orientation-edge
filtration, full segment Jacquet formula, Aubert irreducible-image theorem,
or excluded classification conclusion.

The recursive project import audit at Library base
`8c5ba55d80ead022f06e4c04ae7621d1f734bac3` contains 629 modules: the supplied
scalar-separated subobject helper and 628 published project modules. Every
published Lean/Markdown pair matches that base. The closure contains no
excluded multisegment, ordered-head, quotient-coverage, tempered-block,
square-integrable or regular classification conclusion. General analytic
predicates and statement definitions occurring in the lower adjointness
closure are not used as proved conclusions.

Author: Worker 1186.
