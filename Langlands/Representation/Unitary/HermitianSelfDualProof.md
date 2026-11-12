# Hermitian representations: self-duality and the full proof

Author: Worker 143. Module `Langlands.Representation.Unitary.HermitianSelfDualProof`, namespace `Langlands.Renard.CompactRepresentation`.

The theorem `hermitianRepresentationStatements` proves exactly the published proposition `HermitianRepresentationStatements`. This is Renard IV.2.1, Remark 1 in both directions and Remark 2, printed pp.96–97 / PDF pp.102–103 of the French edition dated 9 July 2026. The registered source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, read at both cited pages. The statement pair and its imports are unchanged. The group and carrier universes remain independent and no hypothesis is added.

## Self-duality implies admissibility

Suppose `e : V ≃ₗ⋆[ℂ] SmoothDual π` is equivariant. For every compact open subgroup `K`, restrict `e` to obtain a conjugate linear equivalence between `V^K` and the fixed space of the smooth dual. Compact fixed restriction identifies the latter with the full algebraic dual of `V^K`. Composing with conjugation in a chosen basis gives an ordinary linear equivalence of `V^K` with its algebraic dual. Mathlib's `Basis.linearEquiv_dual_iff_finiteDimensional`, an Erdős–Kaplansky corollary, makes `V^K` finite dimensional. For an arbitrary open subgroup choose a smaller compact open subgroup using the published Van Dantzig theorem; the inclusion of fixed spaces proves the required finiteness. This gives the Library's all-open-subgroups admissibility predicate.

## Self-duality gives a hermitian form

The canonical form `B(x,y) = (e x)(y)` is invariant, sesquilinear and left nondegenerate. It need not be hermitian. This proof supplies an additional algebraic symmetrization.

The adjoint form `B*(x,y) = conj(B(y,x))` is invariant and left nondegenerate. To prove its nondegeneracy, surjectivity of `e` reduces vanishing against `B*` to vanishing against every smooth functional. The published injectivity of the smooth bidual map says that these functionals separate vectors.

The general admissible pairing equivalence from `HermitianAdmissibleProof` now applies to `B*`, even without hermitian symmetry. Compare it with `e` to obtain the linear automorphism `T` characterized by

`B(Tx,y) = conj(B(y,x))`.

Both identifications are equivariant, so `T` commutes with every group operator. In particular it preserves each open fixed space. These spaces are finite dimensional by the preceding admissibility argument, and smoothness places each vector in one of them. Thus `T` is locally finite.

Apply `exists_hermitian_of_locallyFinite_asymmetry` from `Langlands/LinearAlgebra/LocallyFiniteHermitian.lean`. That helper splits the generalized −1 eigenspace of `T` from the sum of the other generalized eigenspaces. These are orthogonal for `B`. It uses `i(B − B*)` on the first summand and `B + B*` on the second. Its paired Markdown proves hermitian symmetry, nondegeneracy, and preservation by every commuting isometry of `B`. Taking each group operator as that isometry gives the required invariant hermitian form, proving `hermitianOfSelfDual`.

## Converse, uniqueness and assembly

`HermitianAdmissibleProof` proves `selfDualOfHermitian` using the injective smooth-dual pairing map and finite dimensional compact fixed restriction. It proves `hermitianFormUniqueness` by comparing the two form identifications, applying admissible Schur, and using hermitian symmetry to make the nonzero scalar real. Its paired Markdown explains both implemented arguments.

The final theorem is the direct conjunction of `hermitianOfSelfDual`, `selfDualOfHermitian`, and `hermitianFormUniqueness`, with exactly the original proposition as its type. The helper constructions are derived implementation content; they neither weaken the target nor assume any of its three assertions.
