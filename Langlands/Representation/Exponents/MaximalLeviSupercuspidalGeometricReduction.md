# The maximal-Levi length bound from the geometric lemma and VI.5.3(ii)

`maximalLeviSupercuspidalLengthBound_of_geometricLemma_noSupercuspidal` proves the
exact represented maximal-Levi induction-length statement through
`maximalLeviSupercuspidalJacquetLengthWitness_of_geometricLemma_noSupercuspidal`,
which constructs the full actual Jacquet-family witness. Both are conditional on two
inputs: `RepresentedGeometricLemmaStatement.{u,v}` and
`LeviJacquetInductionNoSupercuspidalStatement.{u,v}`. These are explicit
premises of this helper. This is an internal reduction following the first
paragraph and numerical argument of Renard VI.5.4, printed pp.173–174 / PDF
pp.179–180, with V.4.8 supplying the maximal-Levi numerical motivation.

The actual-image count constructs a finite separated family of parabolics with
the original embedded Levi. The geometric lemma supplies actual double-coset
enumerations, representatives, intersection data and natural finite filtrations
for every target in this family. The coordinate-free survivor budget bounds the
total number of full-source indices by two.

For an arbitrary irreducible actual subquotient of the induced representation,
Worker 4949's `exists_conjugateLevi_supercuspidal_jacquetQuotient` uses the proved
VI.2.1 and exactness of Jacquet functors, together with the VI.5.3(ii) input, to
produce a nonzero Jacquet module along a parabolic with a conjugate embedded
Levi. The family's coverage selects a rationally conjugate target.
`nontrivial_leviJacquet_of_range_eq_comp_innerIso` transports nontriviality to
that target even though its Levi and radical presentations may differ. This
establishes detection of every irreducible subquotient. The existing exact
Jacquet-family length bound then proves the conclusion.

No finite-length assumption, standard-parabolic realization, Coxeter system,
root comparison, supplied detecting family or VI.5.4 association is used. The
field and carrier universes remain independent and the topologies are the
canonical ones in the original target. This helper does not discharge either
of its two named representation-theoretic inputs.

The additional theorem
`maximalLeviSupercuspidalLengthBound_of_geometricLemma_properInductionExclusion`
uses Worker 1781's `leviJacquetInductionNoSupercuspidal_of_geometricLemma` to
replace VI.5.3(ii) by the proper-induction exclusion of VI.5.2. Finally,
`maximalLeviSupercuspidalLengthBound_of_geometricLemma_cuspidalSplitting` uses
the published
`leviInductionNoSupercuspidalSubquotient_of_cuspidalRemainderSplitting` to reduce
VI.5.2 to `RepresentedCuspidalRemainderSplittingStatement.{u,max u v}`. Thus the
remaining exact prerequisites can be taken to be the represented geometric
lemma and the objectwise cuspidal/remainder splitting. Neither is proved here.

`maximalLeviSupercuspidalLengthBound_of_cuspidalSplitting` applies this last
reduction to the published unconditional `representedGeometricLemma` from
`RepresentedGeometricLemmaProof`. Its only premise is therefore the exact
`RepresentedCuspidalRemainderSplittingStatement.{u,max u v}`. The final
unconditional length bound remains open until that splitting is proved.
