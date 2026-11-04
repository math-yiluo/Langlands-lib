# Detection from finite restriction to the actual rational norm kernel

`rationalNormKernelFixedVectorDetection` proves the published internal proposition `RationalNormKernelFixedVectorDetectionStatement`, retaining its explicit finite-restriction and compact-coefficient premises.

The proof takes the actual normal subgroup \(H=\texttt{Plancherel.rationalCommonNormKernel G}\). The published closedness theorem gives local compactness of \(H\), while the inherited nonarchimedean topology and Hausdorff property give total disconnectedness. Equip \(H\) with its Borel measurable structure and a Haar measure. The compact subgroup \(K\) lies in \(H\) by `compactSubgroup_le_rationalCommonNormKernel`.

Apply the finite-restriction premise to \(D\). It supplies a finite family of irreducible actual subrepresentations of the restriction spanning the whole carrier. Irreducibility of \(D\) implies that its carrier is nontrivial. An empty index type would make the supremum the zero submodule, contradicting this nontriviality. Thus the finite family is nonempty.

Compact open subgroups are cofinal among open subgroups of \(H\), by the existing test-function neighborhood theorem. `hasCompactSmoothDualCoefficients_subrepresentation` then transfers the assumed compact smooth-dual coefficients of the full restriction to each member of the finite family. The published `compactRestrictionFixedVectorDetection` applies with this family, the original generation hypothesis, and the original subquotient relation, giving the required nonzero \(K\)-fixed vector.

This is an internal assembly proof using the published interfaces described in the statement's Markdown. The semisimplicity and finite-length components of the finite-restriction premise are not needed separately: its finite spanning family suffices. No actual finite-restriction theorem, cuspidal compactness theorem, geometric compact-open choice, or final Howe implication is asserted here.
