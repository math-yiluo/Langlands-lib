# Actual rational geometry for cuspidal Jacquet-factor extraction

Worker 321, with Worker 1553's audit of the published full-Levi comparison.
This internal derived construction supplies the geometric subgroup and
single-term comparisons needed by the actual cuspidal Jacquet-factor
extraction task. It does not supply the normalized geometric filtration or
exclude cuspidal subquotients from proper target induction.

For a minimum `w` in `IsMinimal cs J I w`, suppose the intrinsic source
intersection `intersectionSubset cs J I w` is all of `I` and the inverse
intersection `intersectionSubset cs I J w⁻¹` is all of `J`. The theorem
`rootAssociation_of_full_intersections` proves `rootAssociation I J n`
for every supplied normalizer lift `n` of this same `w`. It rewrites
`intersectionSubset_eq_simpleImage_inter` at `w` and, using
`isMinimal_inv`, at `w⁻¹`. The two simple-image intersections in the
published `rootSet_simpleImage_intersections` are therefore precisely `I`
and `J`. The quotient equality for the supplied lift proves the actual
character image in the definition of root association. In particular,
positivity comes from the published root comparison theorem; conjugacy
of simple reflections alone is not used to infer a signed character image.

`pointGeometricTerm_full_intersections` uses this association to obtain
`conjugationMembership_of_rootAssociation` for that same rational point.
It applies `geometricTermFullLeviIso` with target/source indices `J I`
and that exact dependent membership witness. The result is an actual
isomorphism from the geometric term on `σ` to
`(conjugationFunctor n hn).obj σ`. Its action is inverse conjugation,
`x ↦ σ(n⁻¹ * x * n)`. Source and target decomposition witnesses are
arbitrary supplied witnesses. No irreducibility or cuspidality condition
on `σ` is needed for this comparison.

The Prop-valued `PointCuspidalExtractionGeometry` groups four proved
inputs for one actual point Coxeter system: the three structural source
intersection identities, actual source and target semidirect
decompositions, vanishing of terms with proper source intersection on
cuspidal data, and the preceding full-intersection conclusion. In the
vanishing part it retains the published `IsCorollaryLeviCuspidal`
condition, equivalent to the original `IsLeviCuspidal` predicate. It
contains no filtration assertion or proper-target exclusion.

`pointCuspidalExtractionGeometry_of_rootComparisons` assembles these
inputs using `pointSourceIntersectionIdentities`,
`geometricIntersectionDecompositions_of_pointSource`,
`pointCuspidalGeometricTermVanishing_of_rootComparisons`, and the new
full-intersection comparison. The proper-source vanishing theorem uses
the original inside-Levi Jacquet vanishing condition; no induction
finite-length theorem is involved.

Finally, `rootSpanPointCoxeterData_cuspidalExtractionGeometry` proves this
package for the system chosen by `rootSpanPointCoxeterData` from the
displayed `HasRelativeRootSystem` witness. Its root-length field and
`positiveSimpleReflectionComparison_of_rootLength` supply both required
root comparisons. The existing data also supplies finite simple roots,
finite point Weyl group and the actual standard-Levi Weyl identification.
The new theorem needs no additional root-comparison premise.

The scope is an arbitrary field in universe `u`, a connected reductive
group scheme, its maximal split torus and generic cocharacter, with the
displayed affine and monomorphism instances and finite actual simple-root
labels. The topological comparisons use the canonical rational-point
topology, local compactness, the nonarchimedean group structure and closed
standard Levis and radicals. They retain the existing
`StandardCocharacterStatement` and `StandardLeviIntersectionStatement`.
Representation carriers have universe `max (u + 1) v` with independent
`u` and `v`. No nonempty-root, positive-rank, split-group,
characteristic-zero or representation finiteness premise is imposed.

The provenance is internal composition of the named published actual
root, subgroup and functor comparisons. Renard, *Représentations des
groupes réductifs p-adiques*, French edition of 9 July 2026, Proposition
VI.5.3(ii),(iii), printed p.173/PDF p.179, motivates the full-intersection
survivor. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The new proofs invoke no classification, adjointness or geometric-filtration
theorem. A proof of the full extraction target still needs an actual
normalized geometric filtration and proper-induction exclusion; this
supporting package does not discharge either obligation.
