# The normalized Jacquet expansion of the regular elementary traces

`RegularElementaryNormalizedJacquetStatement` takes the unnormalized
regular elementary Jacquet trace formula in each of two independent
field and representation universes. For a cyclic unramified extension
\(E/F\) of degree \(\ell\), it computes the traces of the two tests in
`regularElementaryBaseChangeTests`. An upstairs intertwiner must act
as the identity on the integral-diagonal fixed space of the Borel
Jacquet quotient. The downstairs trace is ordinary.

At a strict integer weight \(\nu\), the two traces are
\[
  c_\nu \sum_{z \in M_E}\prod_i z_i^{\nu_i}, \qquad
  c_\nu \sum_{z \in M_F}\prod_i z_i^{\ell\nu_i},
  \qquad c_\nu = q_E^{\rho(\nu)}\sqrt{q_E^{-\rho(\nu)}} .
\]
Here \(M_E\) and \(M_F\) are the multisets `borelJacquetMultiset` of the
respective irreducible admissible representations. The sums count
generalized weights with their multiplicities. The factor is nonzero
because \(q_E\) is positive.

The equal fixed submodules from `borelJacquetNormalization` give a
linear equivalence that preserves vectors in the Jacquet quotient.
Conjugating the unnormalized diagonal action by this equivalence
gives the normalized lattice action times the positive half-modulus.
The lattice action depends only on the orders of the entries. The
trace is invariant under this conjugation, and `borelJacquetWeightTrace`
computes the trace of the normalized action. The hypothesis on the
upstairs intertwiner removes its restriction from the trace.

The base uniformizer has order one in \(E\) and is fixed by the
generator. The ordinary trace uses the base uniformizer at weight
\(\ell\nu\). Since the absolute ramification indices agree, the
degree identity for the two towers over \(\mathbb Q_p\) gives
\(q_E=q_F^\ell\). The definition of `regularElementaryRho` gives
\(\rho(\ell\nu)=\ell\rho(\nu)\). These identities give the same factor
for both traces.

The normalized character sum and the half-modulus in this calculation
come from Henniart–Lemaire, *Changement de base et induction
automorphe pour GLₙ en caractéristique non nulle* (2011), I.5.3 and
I.5.4, Lemma 2 and its proof, printed pp. 31–35 (PDF pp. 39–43).
The Lean proof uses the finite-dimensional integral-diagonal fixed
space and its generalized weight decomposition.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
