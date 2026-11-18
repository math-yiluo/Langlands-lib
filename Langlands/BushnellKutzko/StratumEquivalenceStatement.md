# Invariants of equivalent strata (T5)

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Proposition (1.5.2),
printed p. 43, and Proposition (2.1.4), printed p. 50 (PDF pp. 55, 62).

`StratumEquivalenceStatement` is an unproved proposition definition.
For every nonarchimedean local field `F`, finite-dimensional `F`-vector
space `V` and two equivalent strata `S,T`, it asserts:

- equality of their hereditary orders, represented by `chain.order`;
- equality of their integer depths `r`;
- equality of their levels `n` if each parameter has valuation exactly
  minus its level;
- if both strata are simple, equality of `𝔅₁ + 𝔓` and `𝔅₂ + 𝔓`,
  of their critical exponents, of their generated-field ramification
  indices and of their generated-field residue degrees.

The two chains may initially differ. The first conclusion compares
their orders, not their indexed lattice-chain presentations.
After that equality, the second group of conclusions is exactly
(2.1.4) in its common-order formulation. Simplicity supplies the exact
valuation conditions, so equivalent simple strata also have equal `n`.

The lattice `𝔅_i` is the existing intersection
`centralizerLattice chain b 0`; sum of lattices is submodule supremum.
The invariants are the constructions in `ElementFieldInvariants`
on the actual `F[b_i]`, not independent field parameters or assumed
equalities. The field and vector-space universes are independent,
and the only premise beyond the local-field setting is the source's
equivalence, with simplicity required just for its corresponding
conclusions.
