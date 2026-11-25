# Splitting bases for lattice chains

Supporting lemmas for the proof of BK93 §1.1, derived from
`Langlands.BushnellKutzko.LatticeChain` and Mathlib. The index and the
splitting induction are developed for an arbitrary vector space in an
independent universe. The one-chain splitting property is the decomposition along
coordinate lines in BK93 (1.1.7), printed p. 23.

`ordOf hϖ c` is the integer exponent in the uniformizer-times-unit decomposition of a nonzero field element, with the value zero assigned at zero. The uniqueness, product, inverse and integrality lemmas follow from the discrete valuation ring decomposition. Products and inverses explicitly require nonzero inputs.

For a lattice chain, `LatticeChain.lattice_add_period` and
`jacobson_integer_eq_maximalIdeal` identify periodicity with scalar
multiplication by a uniformizer. The union of its lattices is a vector
subspace by `LatticeChain.antitone` and the formula for scaling by a
field element. It is the whole space by `LatticeChain.isLattice`.
Their intersection is zero because in an extended integral basis
of the zeroth lattice a nonzero coordinate cannot have arbitrarily
high uniformizer divisibility. Consequently each nonzero vector has a
greatest lattice index by `Int.exists_greatest_of_bdd`. The function
`LatticeChain.index` assigns that index and gives the zero vector
index zero by convention. Membership and scaling lemmas about this
index carry the relevant nonzero hypotheses.

`LatticeChain.Splits` means that membership of a finite linear
combination in any chain lattice implies membership of each term.
For a basis, this is the direct sum decomposition into its coordinate
lines. The finite-span induction `exists_splits_span` constructs a
basis splitting two chains once one of them has a splitting basis.
It chooses a vector maximizing the bounded integer difference of
normalized indices and removes a coordinate of minimal index from
the spanning family. The chosen vector and the remaining coordinate
hyperplane split each lattice in the current span, using the minimum
coordinate for one chain and maximality of the index difference for
the other. The induction supplies the splitting family on the
hyperplane. Boundedness of the index difference follows from finite
generation, `LatticeChain.period_pos`, and periodicity.
`LatticeChain.standard_splits` gives a splitting basis for the
standard coordinate chain, and applying the induction twice gives
`LatticeChain.exists_basis_splits_both`.

`LatticeChain.linearEquivMap` transports lattices using the
scalar-restricted linear equivalence. It uses the published
`LatticeChain.isLattice`, `LatticeChain.lattice_succ_lt` and
`LatticeChain.exists_period` to preserve finite generation, spanning,
strictness and periodicity. `LatticeChain.exists_basis_splits` extends
a finite integral basis using `Module.Basis.extendOfIsLattice` and
identifies the ambient space with a finite coordinate space. It
applies common splitting there with the transported chain in both
slots and transports the resulting basis back. This covers an
arbitrary `V : Type v` independently of `F : Type u`.
[Lattice chains](LatticeChain.md)
