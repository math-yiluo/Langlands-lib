# Integral automorphisms from stabilizers of realized Tate lattices

This internal result concerns actual abelian schemes A and B over a connected
locally noetherian base where every positive integer is invertible. It retains
the finite-etale torsion premise and an algebraically closed characteristic-zero
geometric point required by the published connected integral reflection theorem.

`RealizedLatticeStabilizerStatement` assumes a rational isomorphism e from B to A
whose full integral Tate image is exactly an additive subgroup L of the full
rational Tate module of A. For a rational self-isogeny a of A whose full rational
Tate operator preserves membership in L in both directions, it asserts an
actual automorphism g of that same B. The rationalization of g and its inverse
are exactly e.hom followed by a.hom or a.inv and then e.inv.

`realizedLatticeStabilizer` proves the assertion. Exact realization converts
preservation of L into preservation of the full integral Tate image by the
conjugated rational homomorphism on B. Two-way preservation for a also gives
preservation by its inverse, using the actual rational Tate linear equivalence.
The published `connectedIntegralLatticeReflection` then produces the integral
automorphism with both required rationalization equalities.

The provenance is an internal consequence of the imported rational Tate
functor, exact realization equation, and proved connected integral reflection.
No existence of a realizing B is asserted here. The result does not construct
a polarization on B or prove finite order of g or a; these remain separate
consumer obligations.
