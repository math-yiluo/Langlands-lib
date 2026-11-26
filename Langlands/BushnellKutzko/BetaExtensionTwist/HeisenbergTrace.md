# Trace support and an intertwining average

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), Proposition (5.1.8), printed p. 160, gives Heisenberg intertwining
multiplicity one. Its proof uses induction from the simple character
and the double-coset count in (5.1.9), derived from the index equality
in (5.1.10), printed pp. 160–162. The Lean argument computes the
intertwining dimension by trace vanishing and finite-quotient character
averaging, using the scalar action and degree identity given by (5.1.1),
printed p. 158. The retained source `bushnell-kutzko-1993-admissible-dual-gln`
has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

`character_eq_zero_of_scalar_index` starts with a finite-dimensional
irreducible complex representation, a normal subgroup on which the
representation acts by a specified scalar character, and the identity
expressing the square of the degree as the subgroup index. Burnside's
theorem gives a spanning family of endomorphisms indexed by quotient
cosets, since any two operators from the same coset differ by a scalar
factor. The index identity makes the family a basis. Left composition
by an operator from outside the subgroup has zero diagonal in this
basis, since the left translation on the quotient fixes no coset.
Its trace is also the trace of that operator times the degree, by the
tensor product description of the endomorphism space. This forces the
operator's trace to vanish.

`finrank_intertwiningMap_mul_index_of_trace_support` applies to two
finite-dimensional complex representations of the same group. Assume
the representation on linear maps between their spaces acts trivially
on a normal subgroup of finite index and has trace zero off that
subgroup. The representation on linear maps descends to the finite
quotient, where the character is supported at the identity. Averaging
computes the dimension of its invariants, which are the intertwining
maps. Multiplication by the subgroup index gives the dimension of the
full space of linear maps.
