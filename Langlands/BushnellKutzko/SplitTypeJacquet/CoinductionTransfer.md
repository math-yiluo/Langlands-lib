# Tensor intertwiners and finite-index coinduction

For a finite-index subgroup \(H \le G\), `finiteIndexCoindHomEquiv` identifies the
\(G\)-intertwiners from \(\operatorname{Coind}_H^G \kappa\) to \(\pi\) with the
\(H\)-intertwiners from \(\kappa\) to the restriction of \(\pi\). It uses Mathlib's
isomorphism from induction to coinduction followed by the induction–restriction
adjunction. Lifting the coefficient modules to a common carrier universe lets
the group and both module carriers have independent universes.

For two finite-index subgroups \(H,K \le G\), `coinducedTensorHomEquiv` takes
equivalent \(G\)-coinductions of \(\kappa\) and \(\sigma\), respectively, and a
representation \(\xi\) of \(G\). It identifies the \(H\)-intertwiners from
\(\kappa\otimes \xi|_H\) to \(\pi|_H\) with the \(K\)-intertwiners from
\(\sigma\otimes \xi|_K\) to \(\pi|_K\). Currying places the common factor in the
target \(\operatorname{Hom}_{\mathbb C}(\xi,\pi)\), with its conjugation action.
Frobenius reciprocity and the given coinduction equivalence transfer the curried
intertwiner, and inverse currying restores the tensor product.

The tensor transfer is used in the containment argument of Bushnell and Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993), proof of
(8.3.5), printed p. 296 (PDF p. 308). There the two subgroups induce the same
representation to \(U(\mathfrak B)U^1(\mathfrak A)\), and an ambient extension of
the finite factor provides the common twist. The equivalence here expresses
that transfer on Hom spaces.
