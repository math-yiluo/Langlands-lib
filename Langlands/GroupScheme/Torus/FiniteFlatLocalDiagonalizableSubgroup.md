# Finite flat local closed subgroups of diagonalizable groups

This derived internal development constructs a diagonalizable presentation for
finite flat affine closed subgroups over every commutative local ring,
including nonreduced rings. It uses the full coordinate character group and
actual group-scheme isomorphisms. Finiteness of the subgroup is a hypothesis;
the arbitrary-base fibrewise central-isogeny criterion
`ReductiveFibrewiseCentralIsogenyStatement` is not proved here but by
`reductiveFibrewiseCentralIsogeny` in `Reductive.FibrewiseCentralIsogenyProof`.

## Coalgebra and bialgebra reconstruction

Let `R` be a commutative local ring and `C` an `R`-coalgebra. The theorem
`groupLike_mem_basis` says that if a finite basis consists of group-like
elements, every group-like element of `C` equals a basis vector. For a
group-like element `g`, write its coefficients in that basis as `a_i`.
Applying the counit gives `∑ a_i = 1`. Since `R` is local, at least one
coefficient `a_i` is a unit. Applying the tensor-product basis coordinates to
`Δ(g) = g ⊗ g` gives `a_i a_j = 0` for `j ≠ i` and `a_i² = a_i`.
Cancellation by the unit forces `a_i = 1` and every other coefficient zero.
Thus `g` is exactly the corresponding basis vector.

If `C` is finite and flat as an `R`-module and its group-like elements span,
`exists_groupLike_basis` constructs a finite basis of group-like elements.
The proof first uses the local-ring theorem that a finite flat module is
free; it is consequently finitely presented. The published
`Module.exists_basis_of_span_of_flat` then extracts a basis from the spanning
group-like family. That theorem implements the residue-field basis and
Nakayama argument. Finite module generation makes the resulting index set
finite.

The preceding characterization of group-like elements makes this basis
bijection with the entire `GroupLike R C` family. Hence that full family is
linearly independent and finite, as proved in
`linearIndependent_groupLike_of_finite_flat` and
`finite_groupLike_of_finite_flat`.

For a finite flat `R`-bialgebra `A` spanned by group-like elements, the
definition `finiteFlatLocalBialgEquiv` constructs

`MonoidAlgebra R (GroupLike R A) ≃ₐc[R] A`.

This is the usual evaluation bialgebra homomorphism on group-like elements.
Its injectivity follows from the proved linear independence and its
surjectivity from the spanning hypothesis, using the Library's general
evaluation and linear-combination lemmas. No domain or reducedness assumption
is used.

## Actual closed subgroups

Let `R : CommRingCat` be a local ring, let `Λ` be any abelian group in the
same universe, and let `H` be an affine group scheme over `Spec R`. Assume
that its structure map is finite and flat, and let `i : H ⟶ D_R(Λ)` be a
closed subgroup inclusion. The entry definition
`finiteFlatLocalClosedSubgroupIso i hi` constructs an actual isomorphism

`H ≅ D_R(Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))`.

There is no finite-generation hypothesis on the ambient group `Λ`.
`finite_characters_of_finite_flat_closedSubgroup` proves that the full
character group displayed here is finite, retaining all torsion.
`isDiagonalizable_of_finite_flat_closedSubgroup` consequently proves
`RelativeMultiplicativeType.IsDiagonalizable H` by comparison with the
published split model over the integers.

The proof transports finiteness of the actual structure morphism through
`AffineCoordinates.hopfSpecIso` and the spectrum criterion for finite ring
maps, yielding module finiteness of the Hopf coordinates. The existing
flatness bridge yields module flatness. Closedness makes the ambient
coordinate map surjective, so its group-like monomials span the subgroup
coordinates. The local bialgebra reconstruction above, the change from
multiplicative to additive indexing, and
`AffineCoordinates.isoOfBialgEquiv` give the actual group-scheme isomorphism.
The finite-character theorem uses finiteness of all coordinate group-like
elements proved in the coalgebra argument.

## Provenance and scope

This is derived internal work based on the Library's actual affine Hopf
coordinates, closed-subgroup coordinate surjectivity, group-like evaluation,
and diagonalizable relative-spectrum constructions. Its local-module input
is Mathlib's finite-flat freeness and spanning-family basis theorem over local
rings. These constructions justify the definitions without introducing a new
source-level convention or assuming an unproved structural statement.

The local-ring hypothesis replaces the domain hypothesis of the related
`FlatDiagonalizableSubgroup` reconstruction, while module finiteness is an
additional essential hypothesis here. The present group-scheme theorem
assumes finiteness of `H`; it does not deduce finiteness from finite fibres.
Neither the general-base closed-subgroup theorem nor kernel centrality in
the central-isogeny criterion `ReductiveFibrewiseCentralIsogenyStatement`,
which this module serves, follows from this module alone.
