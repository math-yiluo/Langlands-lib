# Actual cuspidal conjugation decay in relative semisimple rank zero

`RationalCuspidalConjugationRankZeroStatement` gives the complete local
conclusion of Waldspurger VIII.3.1 when the set of simple relative roots is
empty. It uses the original matrix height, Haar measure, intrinsic cuspidal
kernel and full torus chamber in the common norm kernel. The proof works
with any of the compact open Iwasawa subgroups quantified in the original
statement.

The standard subgroup endpoint equalities show that the maximal split torus
is central and that the minimal unipotent radical is trivial. The modulus of
its conjugation action is therefore one, so the Iwasawa weight and its
normalized compact average Xi are identically one. The common norm kernel is
compact by the Library's central maximal split-torus quotient argument,
using the established reductivity of the central quotient and compactness
of anisotropic reductive groups.

The proof of weighted square integrability uses integer valuations on a
basis of rational characters. The kernel of this tuple of valuations is the
common norm kernel. Each nonempty fiber is a left translate of that compact
subgroup and has its Haar measure. The image embeds in the integer lattice
given by the coordinate basis of a real vector space. The character
valuation bounds in terms of the matrix height verify the lattice norm
comparison in `CartanSquareBound`. That theorem gives weighted square
integrability, which gives absolute convergence for every conjugator.

Centrality makes the conjugation pairing constant on the torus image. On
the compact chamber the original height is bounded. Comparing powers of
one plus that height to powers of one provides a single positive constant
for each real decay exponent.

This is a derived case of Waldspurger's 2003 Plancherel article, VIII.3.1,
printed pp. 323–326. The proof uses the rational-character lattice and
compact norm kernel directly to establish the needed square integrability.
