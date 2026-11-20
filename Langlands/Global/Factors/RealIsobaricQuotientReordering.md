# Reordering the real standard module while retaining its quotient

`realStandardQuotientReordering` proves the reordering input of the local
isobaric construction. The quotient by a stable subspace of a real
standard module is first read as a constituent of the compact and real
infinitesimal operators on that module, using the quotient projection
defined everywhere. The operator constituent permutation theorem then
supplies a stable subspace of the reordered module with a surjection
onto the very same quotient.

The compact action is already among the operators of the permutation
theorem. Stability under each real Lie direction implies stability under
the complexified Lie algebra, by linearity on pure tensors and addition.
The same extension applies to the equivariance identity for the
surjection. Thus the resulting subspace and map carry the full actions
asked for by `RealStandardQuotientReorderingStatement`.

`realIsobaricPlaceQuotientReduction` uses this reordering in the real-place
construction. Its two remaining inputs are the real generic standard
parameter theorem and irreducibility of real standard modules with tied
real exponents. It gives the ordered quotient of the actual cuspidal
parameters as a constituent in the supplied order.

This implementation uses the actual permutation theorem for real
standard modules. The comparison of constituents is motivated by
Badulescu and Renard (2010), Remark 2.3 and Proposition 2.4, printed
pp. 1123–1124 (PDF pp. 10–11). The local isobaric application is Getz
and Hahn (2024), Theorem 10.6.4, printed p. 286 (PDF p. 298).
