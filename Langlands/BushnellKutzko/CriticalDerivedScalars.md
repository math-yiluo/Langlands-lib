# Scalar recognition and nonvanishing at the critical depth

Internal lemmas for the proof of Bushnell–Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), registered
`bushnell-kutzko-1993-admissible-dual-gln`, (2.4.1)(iii), printed p. 65.
These arguments use the lattice-chain splitting and adjoint filtration
rather than the book's particular representative in §2.4.

For a normalizing field `K`, `rankOne_mem_endFiltration` generalizes the
order-level rank-one map for a splitting basis: a basis vector scaled to
have exact depth zero can be sent to any vector of depth at least `i`
by a `K`-linear rank-one operator in degree `i`.
`exists_scalar_of_graded_commutation` chooses a scalar by projecting the
image of that reference vector onto its `K`-line. Commutation with the
projection modulo the next depth proves agreement there. Commutation
with the rank-one operators, in all degrees, proves agreement with the
same scalar on every layer. The ambient endomorphism itself need not be
`K`-linear.

`graded_commutation_of_approx` transfers commutation modulo the next
depth from the approximating operators in the `γ`-centralizer to operators
commuting with `β`. Finally, `not_mem_succ_of_critical` shows that the
derived symbol cannot be zero at a critical index of `β`: since the
adjoint lattices at that index are unchanged by the depth-`d` perturbation,
vanishing would allow every element of the adjoint lattice to be corrected
first to the `γ`-centralizer and then to the `β`-centralizer modulo depth
one, contradicting criticality. Both correction premises are explicit
in this lemma.
