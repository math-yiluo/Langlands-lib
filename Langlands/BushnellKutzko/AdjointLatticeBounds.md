# Bounds for the adjoint lattice filtration

This module proves the intersection in Bushnell–Kutzko (1993), (1.4.4),
and the upper bound needed for the definition in (1.4.5), printed p. 36.
It uses the periodic chain and endomorphism filtration of §1.1,
printed pp. 19–21.

The period formula for the vector lattices identifies one period with
multiplication by the base uniformizer. Applying the formula to the
values of an endomorphism gives the corresponding filtration formula.
Krull intersection on the zeroth lattice separates the vector chain.
It also separates the endomorphism filtration because the zeroth lattice
spans the vector space. Thus an element lying in every adjoint lattice
belongs to the order and has zero commutator.

Every vector enters a prescribed lattice after multiplication by some
uniformizer power. Such vectors form a base-field submodule containing
the lattice, since field scalar denominators are products of units and
uniformizer powers. Finite generation then gives a common uniformizer
power for the image of the zeroth lattice under any endomorphism.
Controlling that image at the desired depth plus one period suffices
for the first period of the chain. Periodicity and base-field linearity
extend the bound to every integer index.

Restricting to the zeroth lattice embeds the order into a finite module
over the integer ring. A linear section of the commutator on its image
therefore carries a sufficiently deep filtration step into step one,
by clearing denominators on finitely many generators of the order.
For elements with commutator in that deep step, subtracting the section
value leaves an element of the integral centralizer. This gives the
upper bound on the critical-index set.
