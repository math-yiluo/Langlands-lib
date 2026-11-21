# Rational Cartier comparison and composition of split rigidifiers

`rationalSplitBaseChangeIso` is the split tower comparison in the
category of actual rational morphisms. `baseChangeDualIso_rational`
shows that the Cartier comparison is natural there. On a pure tensor
this is naturality for the integral dual map, with the same scalar on
both sides. Additivity gives the equation on the full rational Hom.

`splitRigidifier_trans` computes composition in the split presentation.
The primal maps compose in their given order. On the dual factor,
Cartier duality reverses the order of the inverse primal maps, and the
two scalar multipliers multiply. This is a calculation with actual
quasi-isogenies of the finite torsion towers.

The split presentation comes from Rapoport–Zink (1996), §6.43, printed
p. 309 (PDF p. 321), before (6.17). Harris (1997), Appendix, printed
pp. 113–114 (PDF pp. 39–40), uses composition of the special-fibre
rigidifier with a frame similitude and with inverse Frobenius.
