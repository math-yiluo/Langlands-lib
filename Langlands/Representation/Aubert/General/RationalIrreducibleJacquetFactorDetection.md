# Rational irreducible Jacquet detection from factor extraction

Authors: Worker 658, with the common-factor assembly route of Workers 55
and 78. This internal application remains conditional on the exact
`RationalCuspidalJacquetFactorExtractionStatement.{u, v}`. It does not
prove that statement or complete the detection task.

`rationalAssociatedJacquetWitnessOfCuspidalFactors` supplies the certified
standard index and actual point of the irreducible Jacquet detection
target at fixed rational-point data, assuming the exact extraction
predicate at those data. The companion theorem
`rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`
has precisely the full rational extraction proposition as its additional
parameter and proves the full rational detection proposition from it.

## Scope and implemented application

The local field universe `u` and carrier parameter `v` are independent,
and the representation carrier universe is `max (u + 1) v`. The group is
literally `RationalPoint k G.X` at `pointTopology`, with the actual standard
parabolic, Levi and unipotent families and literal `SimpleRoot i ν`
labels. The global theorem retains every premise of the unchanged
support-category target, including Hausdorffness. The fixed-data helper
uses only local compactness and the nonarchimedean group structure.
Positive characteristic, nonsplit and non-quasisplit groups, empty
simple-root sets and relative rank zero are retained.

The application discharges three of the generic reduction's four inputs:

1. For each irreducible `A`, simplicity of its monoid-algebra module
   supplies `Nontrivial A`. Worker 78's
   `exists_irreducible_cuspidal_jacquet_subquotient` then supplies a
   nonzero standard Jacquet module and an irreducible cuspidal actual
   subquotient of that same module.
2. Worker 12's public `isLeviCuspidal_conjugation` transports the
   proper-standard inside-Levi vanishing predicate for each supplied
   root association and Levi membership equivalence.
3. Worker 78's public `rootAssociation_mul` composes the actual
   representatives in the order `m * n`.

The remaining input is exactly the displayed
`CuspidalJacquetFactorExtractionTarget` at these families. Applying
`associatedJacquetWitnessOfCuspidalFactors` therefore returns the
simultaneous association and Levi comparison at the same point, together
with nontriviality of the chosen normalized Jacquet module. The whole
proposition theorem installs the affine and monomorphism instances from
reductivity and maximal splitness, installs the given finite simple-root
enumeration, specializes its sole extra extraction parameter, and unpacks
the certified witness.

## Dependencies and provenance

The argument is internal application of Library declarations. The
generic witness manipulation is explained in
[IrreducibleJacquetFactorDetectionReduction](IrreducibleJacquetFactorDetectionReduction.md).
The substantial factor construction is Worker 78's
[RationalCuspidalJacquetSubquotient](RationalCuspidalJacquetSubquotient.md),
which uses the published minimal nonzero Jacquet construction, unrestricted
irreducible subquotient existence, and actual Jacquet exactness. Its inner
compact-limit premises follow from the displayed `hStandard` and closedness
of the chosen Levi, through
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
and `isLimitOfCompactSubgroups_subgroupOf`; no compact-limit premise is
added here. This application invokes no cuspidal induction embedding or
parabolic quotient compactness theorem.

The cuspidality transport dependency is Worker 12's
[RationalSupportAssociationInvariance](RationalSupportAssociationInvariance.md).
Its implementation compares the actual inner normalized Jacquet functors
under the supplied continuous conjugation, using proper nested-root,
Levi and radical transport deduced from the target's structural data.
The representative multiplication is the elementary group-action result
in [RootAssociationComposition](RootAssociationComposition.md).
The two semidirect-decomposition adapters and
`simpleRelativeRootFintype` are precisely those used by the target.

No classification, character-independence, geometric-lemma or adjointness
theorem is invoked to discharge these three inputs. The generic extraction
input retains its separate geometric-lemma and transport obligations;
this conditional pair makes no assertion about the proof dependencies
of a future theorem discharging it.

The 1 local instance has module-specific names to prevent generated-name
collisions when related modules are imported together. The instance types,
bodies and local scope are unchanged.
