# Passage from formal order-linear rigidifiers to the split towers

`QuasiIsogeny.pDivisibleMap` takes a formal order-linear quasi-isogeny
and restricts it to the actual scalar torsion levels in both directions.
The formal commutation equation maps to the actual rational tensor
under restriction. Preservation of composition and the integral
inclusion identifies the resulting equation with commutation with
the order action on the two towers.

`splitPDivisibleRigidifier` combines this primal map with its scaled
inverse Cartier dual. It gives a quasi-isogeny linear for the split
order between the two actual polarized products. The inputs are the
formal modules with scalar divisibility, the formal order-linear
quasi-isogeny, finite Cartier exactness, and the single common
\(\mathbb Q_p^\times\)-multiplier.

Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), uses the
special formal primal module and its Cartier dual, with the primal
rigidifier and its inverse dual in the normalized case. Harris (1997),
Appendix, printed p. 113 (PDF p. 39), condition (iii) of C1, requires
linearity for the full split order and allows the common multiplier.
