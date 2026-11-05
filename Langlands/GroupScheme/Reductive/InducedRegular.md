# Left-covariant coordinate subspaces and finite regular subspaces

Worker 1330 derived this internal coalgebra construction from the Library's left and
right translation operators. Let `K` be a field, `B` a `K`-coalgebra, `C` a `K`-vector
space, `r : B →ₗ[K] C` a linear map, and `χ : C`. The module does not assume that
`r` is a subgroup restriction or that `χ` is a character.

`leftCovariantSubspace r χ` is the subspace of `b : B` satisfying
`(r ⊗ id)(comul b) = χ ⊗ b`. When `B` and `C` are coordinate algebras and `r`
is restriction to a subgroup, this is the coordinate equation for
`f(hg) = χ(h) f(g)`. This module only constructs the displayed linear subspace;
it does not identify it with sections of a line bundle.

`mem_leftCovariantSubspace_iff` identifies membership with the equations
`leftAct (φ ∘ r) b = φ(χ) • b` for every linear functional `φ` on `C`.
For the reverse implication, the Library's `Unipotent.tensor_ext_left`
separates tensors by contraction on the first factor.

`rightAct_mem_leftCovariantSubspace` proves that every right translation
preserves this subspace. Its proof uses commutation of left and right translation
from coalgebra coassociativity and linearity of right translation.
`regularSpan_le_leftCovariantSubspace` applies that stability to the generators of
the finite regular span. Consequently,
`exists_finite_leftCovariant_regularSubspace` places any finite set of covariant
coordinates in a finite-dimensional, right-translation-stable subspace contained
in the covariant subspace.

The full covariant subspace is not asserted to be finite-dimensional. No
highest-weight, Steinberg, irreducibility, self-duality or exhaustion theorem is
proved here, and this module does not prove
`SimplyConnectedPositiveCharConjugationMapStatement`.
