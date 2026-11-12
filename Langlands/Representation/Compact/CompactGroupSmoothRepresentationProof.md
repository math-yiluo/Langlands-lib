# Smooth representations of a compact group

Author: Worker 88. The entry theorem `compactGroupSmoothRepresentation` proves
the exact Library proposition
`Langlands.Renard.CompactRepresentation.CompactGroupSmoothRepresentationStatement`.
It is the IV.1.1 part of `CompactGroupSmoothStatements`; the IV.1.2 multiplicity
criterion is a separate proof obligation.

The original is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.1.1 Theorem, printed p.88 / PDF p.94,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The group and representation carrier have independent universes. The theorem
retains compactness, the Hausdorff property and total disconnectedness,
and requires no additional structure on the representation carrier.

`finiteDimensional_of_compact_irreducible` takes a nonzero vector in the
irreducible representation. The published compact finite-orbit theorem makes
its orbit finite. Its span is therefore finite-dimensional and, by the
published nonzero-orbit spanning theorem, is the entire representation.
This is the source's proof of (i).

`exists_openNormal_trivial_of_finiteDimensional` chooses a finite basis and
an open subgroup fixing each basis vector. Their finite intersection fixes
the whole representation by linear-map extensionality on the basis.
It is contained in the kernel of the action homomorphism to units of the
endomorphism ring. This kernel is normal and is open since it contains that
open subgroup. The kernel itself is the required open normal subgroup.
The helper does not need compactness; the source observes additionally that
open subgroups of a compact group are compact. This proves (ii).

For (iii), give the compact group its Borel measurable structure and choose
Haar measure normalized on the positive compact whole group. Every smooth
coefficient has compact support because the domain is compact. The published
`CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients`
then applies, with no countability or right-invariance premise. Mathlib's
subrepresentation/group-algebra correspondence gives precisely
`IsSemisimpleModule (MonoidAlgebra ℂ K) π.representation.asModule`.
This differs from the source's finite-quotient proof and uses an already
published unconditional semisimplicity theorem.

For (iv), `positiveCore` supplies a positive definite Hermitian form on an
arbitrary complex vector space. Choose an algebraic basis and map a vector
to its finitely supported coordinate function in the square-summable coordinate
space. This is an injective linear map; pulling back the Hilbert-space inner
product gives the required algebraic core, for every carrier universe.
The original carrier is given no norm, topology or completion.

`averagedPositiveForm` integrates that core evaluated on the inverse orbits
of both arguments. Each scalar pairing is locally constant, by smoothness,
and hence continuous and integrable on the compact group. The integral is
Hermitian, additive and conjugate linear by the scalar integral identities,
and is positive semidefinite. If the integral on a diagonal vector vanishes,
nonnegativity makes its real part vanish almost everywhere. Continuity and
positivity of Haar measure on nonempty open sets make it vanish everywhere,
in particular at the identity. Definiteness of the original core forces the
vector to be zero. Left translation in the integral proves invariance under
the group action: inverse orbits convert applying `h` to translating the
integration variable by `h⁻¹`. Thus only left Haar invariance is used.

The measurable structure and Haar measure are constructed inside the entry
proof. They add no premises to the exact target. The latter two arguments
are internal derivations from published Library results and pinned Mathlib
integration and inner-product-space infrastructure.
