# Admissible hermitian duality and uniqueness

Author: Worker 143. Module `Langlands.Representation.Unitary.HermitianAdmissibleProof`, namespace `Langlands.Renard.CompactRepresentation`.

This proves `SelfDualOfHermitianStatement` and `HermitianFormUniquenessStatement`, the admissible converse in Remark 1 and the scalar uniqueness in Remark 2 of Renard IV.2.1, printed pp.96–97 / PDF pp.102–103 of the French edition dated 9 July 2026. The registered original is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Implemented proof

An invariant sesquilinear form sends a smooth vector to a smooth functional: every subgroup fixing the vector fixes its functional. This gives the conjugate linear equivariant map `HermitianProof.pairingToSmoothDual`. Nondegeneracy gives injectivity.

For an admissible representation this map is surjective. Given a smooth functional, choose a compact open subgroup fixing it, using the published Van Dantzig theorem. Compact fixed vector duality identifies the smooth dual fixed space with the algebraic dual of the original fixed space. At that finite dimensional level the conjugate linear map is injective, and the source and target dimensions agree. Compose with conjugation in a chosen basis to apply the ordinary linear dimension theorem. Surjectivity at the chosen level and injectivity of compact fixed restriction give the original functional. The resulting `pairingEquiv` has exactly the prescribed evaluation and equivariance. This argument in fact uses only invariance and left nondegeneracy; hermitian symmetry is unnecessary for this step.

For uniqueness compare the two conjugate linear equivalences to obtain a linear equivariant automorphism. The published admissible Schur theorem makes it a scalar `z`. Evaluation gives `B' = conj(z) B`. Irreducibility makes the representation nonzero. Left nondegeneracy supplies a nonzero value of `B` and shows that `conj(z)` is nonzero. Hermitian symmetry gives `conj(z) = conj(conj(z))`, so this scalar is the embedding of its real part. That real part is the required nonzero real scalar.

The helpers in `HermitianProof` are internal derived constructions supporting these proofs and the remaining self-dual implication. They do not assert that an arbitrary self-dual sesquilinear pairing is already hermitian. The first implication and the full conjunction are not proved in this module. All original group hypotheses and the independent group and carrier universes are retained.
