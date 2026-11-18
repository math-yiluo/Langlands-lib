# Multiplicative shifts of a lattice chain

The stabilizer of a strictly decreasing lattice chain acts on its integer
index by translations. The shift of a product is the sum of the shifts,
because the composite of the two actions carries any lattice to the
lattice with that index. A stabilizer unit has order valuation equal to
its shift, since containment between two lattices is equivalent to the
reverse inequality between their indices.

`LatticeChain.fieldShift` restricts this action to an embedded field whose
units stabilize the chain. Its target is the additive group of integers
written multiplicatively. The accompanying membership lemma describes
multiplication by a field unit on each lattice. The integrality lemma uses
a monic polynomial relation. If a root had negative shift, its highest
power would carry the lattice onto a strictly larger lattice than the one
containing all terms of lower degree. The relation would then contradict
strict decrease.

These are derived lemmas for the proof of Bushnell–Kutzko (1993),
Proposition (1.4.15). The shift and order filtration are those built from
the lattice-chain setting in §1.2, printed pp. 24–25, of
`bushnell-kutzko-1993-admissible-dual-gln`.
