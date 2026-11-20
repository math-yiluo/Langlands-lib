# Symmetries of proper Fourier synthesis in VIII.2.2

`properFourierSynthesis` applies the actual source-weighted synthesis to the
finite-support smooth lift of the proper Fourier cutoff. The lift requires
smooth proper Fourier components and finite support of the proper part. The
strictly lower-rank finiteness input and the preceding support comparisons
supply the latter.

At a proper index, the cutoff retains the full Fourier component. The
coefficient evaluated at an actual inducing representative equals the Schur
degree times the induced Schwartz character evaluated on the left translate
of `check f`. The proof applies the representative formula for the actual
source coefficient and then VII.1.1(iii).

`ProperFourierSynthesisSymmetryStatement` gives the three identities for
the term subtracted in VIII.2. The inputs are the actual induced character
equalities and the proper-orbit comparisons of measure, degree and density.
The coefficient formula makes the Schur degree a real scalar. At each
parabolic the orbit comparison matches representatives, so the character
equalities compare the integrands after the specified change of variables.
The continuity of the actual density and coefficient on a compact unitary
orbit gives integrability for its finite normalized Haar measure. The proof
uses real linearity to commute the value operations with these integrals.
Conjugation uses the reality of the density, and twisting uses its invariance
under the actual unitary twist.

The induced permutation of the full index fixes each parabolic. It
preserves the real source coefficient, and the value of each group
component is zero after the cutoff. The proof reindexes the finite sum
using these pointwise identities. The hypotheses for this reduction use
only finite support of the proper part. The field and representation-carrier
universes remain independent. The operator identities use this comparison
once the proper synthesis is taken in the Schwartz space.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)*, Journal of the Institute of Mathematics of
Jussieu 2 (2003), VI.3, VII.1.1(iii), and VIII.2.2 on printed p. 322.
[DOI](https://doi.org/10.1017/S1474748003000082)
