# Rank-one outer type-A models and their local dimension bound

This internal result combines published Hermitian presentation, split-rank,
unitary splitting, and local dimension theorems. It applies to the actual
Cartan matrix and full absolute Galois star action of a supplied Tits index.
The field universe is arbitrary and there is no characteristic restriction.

For a separable quadratic extension `L/K`, an actual all-test presentation
of an affine, locally finite-type group scheme `G` by a nonsingular Hermitian
matrix on `Fin (n + 1)`, with `n ≥ 1` and `splitRank G = 1`, gives the existing
`HermitianRoot.SchemeModel.RankOneModel K L n G`. These data retain a diagonal
Hermitian form on `Fin (n - 1)`, units equal to its weights, anisotropy of that
middle form, and an actual isomorphism from `G` to its Hermitian root model.

The proof extracts the natural injective matrix homomorphisms from the
presentation. The published split-rank upper bound and the presentation's
Witt-index lower bound identify its attained Witt index with one. A maximizing
totally isotropic subspace supplies attainment, and the presentation's lower
bound controls every totally isotropic subspace. The existing attained Gram
coordinate construction and all-test scheme comparison then give the model.

For a simply connected absolutely almost-simple group with an actual type-A
numbering and nontrivial full star action, `UnitaryInvolutionSplitting K`
supplies such an all-test Hermitian presentation. Nontriviality of the star
action forces `n ≥ 2`. At split rank one the first construction therefore
gives `OuterTypeARankOneHermitianModel K G n`, without assuming any
distinguished positions. The theorem
`nonempty_outerTypeARankOneHermitianModel_of_unitarySplitting` states this
existence over any field satisfying that splitting property.

Over a nonarchimedean local field, the published commutativity theorem for
division algebras with a unitary involution supplies the splitting property.
`localOuterTypeARankOneHermitianModel` chooses the resulting actual model.
The published bound for anisotropic diagonal Hermitian forms gives
`n - 1 ≤ 2`. Together with `n ≥ 2`, this proves
`TitsIndexData.rank_one_outer_A_rank_bounds`: `n = 2 ∨ n = 3`.
The Hermitian bound uses the all-characteristic local quadratic dimension
theorem, so field and residue characteristic two are retained.

The provenance is internal composition of the imported published results.
The tuple type `OuterTypeARankOneHermitianModel` is reused from the earlier
conditional reduction; the new construction replaces its supplied
presentation and rank propositions by proved inputs. It does not use the
rank-one classification or a local Kneser--Tits theorem.

This unit does not identify the exact distinguished vertices of the original
index. In particular, it does not yet prove `HasRankOneOuterAIndex` or the
full `LocalRankOneTitsIndexStatement`.
