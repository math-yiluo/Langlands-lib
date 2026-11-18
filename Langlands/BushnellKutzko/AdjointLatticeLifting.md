# Lifting at a specified adjoint lattice depth

This module develops the integral commutator lifting used in Bushnell–Kutzko
(1993), (1.4.7) and (1.4.10), printed pp. 36–38. Write `P(i)` for the
endomorphism filtration and `Q(i)` for its intersection with the
commutator kernel. The mixed adjoint lattice consists of the elements in
`P(m)` whose commutator lies in `P(m+k)`.

The inverse-step identity for the relative filtration gives transport of
both the endomorphism filtration and the mixed adjoint lattices. In
particular, the mixed lattice at `(m,k)` is `Q(m) · N(k)`. At depth
`k+1` above the critical set, the definition of this set gives a
decomposition into a centralizer term and an element of the first
endomorphism step. Transporting the decomposition by `Q(m)` gives a
preimage of the same commutator at depth `m+1`.

To lift an element in the global commutator image at depth `m+k`,
multiply an initial preimage by a power of the base uniformizer until
it lies in `P(m)`. Each uniformizer factor adds a period to the
commutator depth. Repeated application of the preceding decomposition
raises the preimage depth by the same number of steps. Dividing by the
uniformizer power puts the preimage at depth `m`.

For nonemptiness of the critical set, a failure at every depth would
give `P(0) ≤ Q(0) + P(1)`. Relative transport and iteration up to the
base period then give `P(0) ≤ Q(0) + 𝔭_F P(0)`. Nakayama's lemma
implies that `P(0)` commutes with `β`. Clearing scalar denominators
extends this to the entire endomorphism algebra, where centrality would
make `β` a base-field scalar.
