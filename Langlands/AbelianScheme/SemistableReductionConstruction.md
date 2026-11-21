# Finite DVR extensions and geometric semiabelian presentations

`FiniteDvrExtension.ofFiniteField` uses a valuation subring in the given
finite extension field that dominates the original DVR. Its fraction
field is the given field. The local algebra map is the restriction of the
composite through the original fraction field, so the required square
commutes.

`SplitSemiabelianPresentation.ofTorusKernel` takes a smooth surjection
from a commutative group scheme to an abelian variety over an algebraically
closed field. It assumes that the actual scheme-theoretic kernel is a torus.
Splitting over the field and reindexing the finite product of multiplicative
groups gives the required isomorphism with a split torus of natural-number
rank. The constructor chooses a rank and a splitting of the kernel of `q`,
then inserts the supplied abelian variety and quotient map directly into
the presentation. The quotient and quotient-map projection lemmas recover
these inputs by reflexivity.

## Provenance

These constructions translate the local DVR extension and geometric torus
in the semiabelian reduction formulation of Bosch, Lütkebohmert and Raynaud,
*Néron Models* (1990), §7.4, printed p. 181. They use the Library's
valuation extension and torus splitting theorems.
