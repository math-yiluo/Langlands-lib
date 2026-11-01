# One global basis for the actual generalized-weight blocks

Author: Worker 88.

`Langlands.commutingTupleGeneralizedWeightGlobalBasis` proves exactly the
published proposition
`Langlands.CommutingTupleGeneralizedWeightGlobalBasisStatement.{u}`. It has
no additional parameters or hypotheses. The statement and its actual
tuple, block, normalization and character constructions are imported
unchanged.

For every natural rank `d`, finite-dimensional complex vector space
`V : Type u`, and actual commuting invertible tuple `A`, the theorem
chooses local bases `b c` of `generalizedWeightBlock A c`, with index
`Fin (Module.finrank ℂ (generalizedWeightBlock A c))`. It assembles one
ambient basis `B`, indexed by the sigma of these fibers over every
`c : Fin d → ℂˣ`. The local and ambient bases are chosen before any lattice
point. The conclusion is the conjunction of all five published properties:
the embedding equation, common strict upper triangularity of the normalized
differences, off-block vanishing, below-diagonal vanishing, and the
coordinate-character diagonal for every integer lattice point.

## Implemented proof

The auxiliary lemmas are in
`Langlands.IntegerLattice.GlobalBlockBasis`.

1. `normalizedDifference_isNilpotent` proves nilpotence on an actual block
   `W`. For the tuple entry `f = A.1 t` and label `a = c t`, the operator
   `f - a • 1` preserves `W`, since the actual generator preserves it.
   The block lies in `f.maxGenEigenspace a`. Mathlib's
   `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap` proves
   nilpotence on that maximal generalized eigenspace, and
   `Module.End.isNilpotent_restrict_of_le` passes it to `W`. The actual
   normalized difference equals `a⁻¹` times this restriction, as verified
   by the ambient coercion formula. Scalar multiplication preserves
   nilpotence. Finite-dimensionality supplies the Noetherian hypothesis
   needed for the maximal generalized eigenspace.

2. `normalizedDifference_commute` maps commutation in the abelian lattice
   through the actual restricted representation. Thus the original block
   generators commute. Scalar normalization and subtraction of the
   identity preserve their commutation.

3. The main theorem applies the published
   `Langlands.CommutingNilpotentStrictUpperBasis.commutingNilpotentStrictUpperBasis`
   to these actual normalized differences on each block. Choice supplies a
   family of local bases. The generic theorem supplies
   `b.repr (N t (b j)) i = 0` whenever `j ≤ i`, including the diagonal.
   No nilpotence, commutation, basis or triangularity hypothesis is passed
   to callers of the main theorem.

4. `block_action_coordinates` extends the local generator properties to
   every lattice point. It sends the actual block representation, as units,
   through `LinearMap.toMatrixAlgEquiv b`. The normalization identity
   `G_t = c t • (1 + N_t)` gives an upper triangular generator matrix with
   constant diagonal `c t`.

   The lattice points whose matrices are upper triangular and have diagonal
   `coordinateCharacter c` form a subgroup. For multiplication,
   `upper_mul_diag` proves that the diagonal of a product of two upper
   triangular matrices is the product of the diagonals: every other
   summand vanishes. For inversion, `upper_unit_inv` uses Mathlib's
   `Matrix.blockTriangular_inv_of_blockTriangular` and the actual matrix
   unit, without any nonzero-dimension assumption. Then
   `upper_unit_inv_diag` applies the product diagonal formula to the unit
   and its inverse and cancels the nonzero scalar character value.

   Every standard lattice generator belongs to this subgroup. The
   coordinate identity
   `n = ∏ t, (generator d t) ^ n.toAdd t` and the subgroup laws prove
   membership for every `n`. The powers are integer powers. This proves
   the local all-integer upper triangularity and character diagonal in the
   already chosen basis.

5. The main theorem imports
   `Langlands.commutingTupleGeneralizedWeightDecomposition` for independence
   and spanning of the actual block family.
   `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` turns these
   conclusions into an internal direct sum, and
   `DirectSum.IsInternal.collectedBasis` assembles the local bases.
   `collectedBasis_coe` gives the embedding equation. The actual action
   preserves each block; `collectedBasis_repr_of_mem_ne` gives off-block
   vanishing, and `collectedBasis_repr_of_mem` identifies the same-block
   ambient coordinates with those just proved locally.

The direct project dependencies are the published global-basis statement,
the simultaneous generalized-weight decomposition proof, and the generic
commuting-nilpotent strict-upper-basis proof. Mathlib supplies internal
direct sums, the matrix algebra equivalence, generalized-eigenspace
nilpotence and triangular inverse closure. These independently authored
dependencies are reused by import; they are not reimplemented here. The
standalone unipotent binomial theorem is not needed for this proof.

## Scope and provenance

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.III,
printed pp.279–280 / one-based PDF285–286, especially the opening choice
of a single common block triangular basis on printed p.280.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both pages were read directly for this proof.

The all-label sigma basis, intrinsic normalized differences, subgroup
argument and local-to-ambient coordinate comparisons are derived proof
details for the published concrete statement. The source works with a
finite list of nonzero blocks and matrices. This implementation instead
uses every actual generalized-weight label, with empty fibers for zero
blocks. It never assumes that the full label type is finite, and does not
enumerate its support.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
was read at PDF18–19. Its C.III correction groups the complete
scalar-times-unipotent factor under the integer power; the 2026 text
already incorporates this correction. The present subgroup proof does
not use that later binomial expansion.

The result retains arbitrary carrier universe `u`, rank zero, the zero
space, zero blocks and every unit label. In rank zero the lattice product
is empty and the action is the identity. Empty block bases require no
diagonal cancellation at a nonexistent index. The character values used
in the inverse argument are nonzero because they are complex units.
Negative and mixed-sign lattice points are included by subgroup closure
under integer powers. No decomposition, triangularization, supplied basis
or desired conclusion is added to the main theorem's hypotheses.

This proves the global-basis assertion only. It does not assert the
nonzero-block/common-eigenvector characterization, multivariable
scalar-times-unipotent product formulas, completion of Appendix C.III, or
completion of the whole book.
