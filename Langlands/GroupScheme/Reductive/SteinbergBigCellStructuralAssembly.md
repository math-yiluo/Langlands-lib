# Steinberg big-cell assembly with the height input discharged

This internal assembly by Workers 1369 and 669 applies the proved
whole-space height theorem to the existing global host construction.
Three global inputs remain explicit: root-datum existence, full integral
coroot generation for simply connected groups, and dominant highest-weight
existence. This unit does not prove those inputs or the unconditional
`SteinbergBigCellStatement.{u}`.

`splitSteinbergHeightIrreducibility` proves
`SplitSteinbergHeightIrreducibilityStatement.{u}`. For an algebraically
closed field in arbitrary universe `u`, an actual affine group, a supplied
finite split pinning, full integral coroot span, and a prime exponential
characteristic, it applies
`SplitPinning.canonicalRhoSteinbergHeightIrreducibility`. That imported
theorem needs no prime premise. Its conclusion is exactly the existing
interface: at every positive height, a supplied highest-weight
representation implies irreducibility of the actual rational right
regular representation on the entire canonical covariant space, in every
finite standard-indexed basis.

The imported height proof obtains a lower dimension bound from the
original highest-vector Frobenius orbit and an upper bound on the whole
canonical covariant space from same-height Frobenius restriction and the
actual positive-root count. The selected nonzero eigen-row gives an
injective coefficient map from an irreducible rational representation on
the same finite coordinate index. The bounds make that map surjective
onto the entire space, and its intertwining identity transfers
irreducibility. No cyclic subspace replaces the canonical covariant
space, and no target finiteness or irreducibility hypothesis is added.
The highest-weight module remains supplied in this implication.

`steinbergBigCellDataOfStructuralInputs` takes the three remaining global
propositions, an algebraically closed field, a prime characteristic and
an actual affine simply connected group. It fills the original
`SteinbergBigCellInputs` structure with those three premises and the
proved global height interface, then applies
`steinbergBigCellDataOfInputs`. The existing construction obtains an
actual split maximal torus and root-line trivializations from proved
theorems, constructs a pinning using the root-datum premise, obtains full
integral coroot span using the necessity premise, and chooses the required
highest-weight modules using the existence premise.

The result is the existing complete `SteinbergBigCellData G` for the
original group. Its six geometric laws retain arbitrary relative test
schemes, including nonaffine, nonreduced and empty tests. Its seventh law
uses cofinal positive Steinberg heights and finite bases of the whole
specified covariant spaces. The subgroup inclusion and weight coordinate
remain those of the canonical construction.

`steinbergBigCell_of_structuralInputs` applies the existing host-unpacking
theorem with these same four fields. Its conclusion is the unchanged
`SteinbergBigCellStatement.{u}` under exactly the three displayed global
antecedents. The arbitrary universe, field, characteristic and relative
tests are retained.

The provenance is a derived composition of the imported height proof and
the existing host assembly. It introduces no external mathematical
assertion. All reused source pairs are included unchanged; their
independent review and publication requirements remain. The unconditional
host still requires published proofs of the three explicit inputs and
the final exact-target proof.
