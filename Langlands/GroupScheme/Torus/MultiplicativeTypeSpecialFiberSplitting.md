# Actual diagonalizations of local special fibres

`LocalSpecialGeometricFiber.specialFiber_isMultiplicativeType` applies to any
commutative local ring `A` and any group scheme over `Spec A`. If its chosen
geometric fibre at the closed point has multiplicative type, its actual
special fibre along `Spec.algebraMap A (IsLocalRing.ResidueField A)` has
field-level multiplicative type. The proof uses the actual geometric-point
factorization and fibre isomorphism in `LocalSpecialGeometricFiber`,
and the reflection of field-level multiplicative type under every
field extension in `MultiplicativeTypeFpqcTransfer`.

When the residue field is separably closed, `specialFiberDiagonalization`
chooses `SpecialFiberDiagonalization A G`: an actual finitely generated
abelian character group and an isomorphism from the special fibre of its
relative model `D_A(M)` to the special fibre of `G`. The group law and the
full character group, including torsion, are retained. This is exactly the
source and target needed by `MultiplicativeTypeStrictHenselianLiftStatement`.

The construction uses the separably-closed-field diagonalization
of a group of multiplicative type, then composes the affine/relative model
comparison and the relative model's base-change isomorphism. It is a
noncomputable choice, with no uniqueness or naturality assertion.

The ring need not be Henselian, Noetherian, complete or reduced. There are
no smoothness, flatness, presentation, affineness or commutativity assumptions
on the group scheme. Only its closed geometric fibre is used; no other fibre
condition is asserted. The group over `A` is not claimed to be diagonalizable.
This is an internal derivation from the actual residue-field comparison and
the Library's field reflection and diagonalization constructions.
