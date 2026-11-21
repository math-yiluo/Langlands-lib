# Archimedean inverse-transpose pairing

The theorem proves the Library's `ArchimedeanTransposePairingStatement` with a freely varying carrier universe. It applies to every irreducible admissible real or complex GK module at each positive matrix size.

On the real side, Jacquet finite dimensionality and nonvanishing provide a nonzero Jacquet functional. The resulting Frobenius Hilbert closure has genuine smooth globalization compatibility with the algebraic module and a unitary orthogonal compact action. Its integrated real test operators are trace class, and their character is a continuous distribution invariant under conjugation.

The real general linear transpose-invariance theorem applies to this character. Decomposing complex inverse kernels into real and imaginary parts gives the corresponding trace comparison on the complex smooth kernel tests. The algebraic trace-to-pairing result uses the continuous inverse-transpose twisted dual and compact trace separation to construct the nonzero invariant complex bilinear pairing. The complex part uses the published algebraic proof `complexTransposePairing`.

This implements the character comparison route in Aizenbud and Gourevitch, *Generalized Harish-Chandra descent and applications to Gelfand pairs*, arXiv:0803.3395v7, Corollary 7.6.3 (p. 22) and Theorem 8.2.1 (p. 23). The real comparison uses the specific Frobenius model of the algebraic module. The statement gives the pairing on the algebraic GK module with the Library's actual compact and complexified Lie-algebra twists.
