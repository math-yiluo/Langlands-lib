# The order and radical filtration relative to a normalizing subfield

`Langlands.BushnellKutzko.subfieldOrder` proves
`Langlands.BushnellKutzko.SubfieldOrderStatement` in independent universes for
the base field, vector space and extension field. The source is Bushnell and
Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(1.2.2)–(1.2.4), printed p. 25 (PDF p. 37), registered as
`bushnell-kutzko-1993-admissible-dual-gln`. [Target statement](SubfieldOrderStatement.md)

The lattice chain makes the vector space nonzero and finite-dimensional over
the base field. Evaluation at a nonzero vector therefore makes the extension
field finite over the base. Its integral closure is a discrete valuation ring
with fraction field the extension field itself. The proof takes
`LatticeChain.subfieldChain` as the relative chain. Its lattices have the same
underlying sets as the base lattices, so the order and filtration comparisons
follow by definition from restriction of scalars. [Chain construction](SubfieldLatticeChain.md)

The spectral local-field structure on the extension identifies integrality
with membership in its valuation ring. The chain from `relativeLatticeChain`
over that valuation ring again uses the same lattice sets. Apply
`radicalFiltration` to this chain. To transfer the product identity, use
induction on membership in a product of filtration steps. Each product
generator belongs to the corresponding product over the integral closure,
and that submodule is closed under addition. The reverse inclusion is the
general multiplicativity inclusion. The two relative orders have the same
elements of `Module.End E V`, so the identity on endomorphisms gives a ring
equivalence. Pull back the Jacobson radical through it to get the radical
comparison over the integral closure. [Radical filtration](RadicalFiltrationProof.md)

The extension uniformizer shifts the base chain by the period of the relative
chain. The base uniformizer has shift the base period and factors as a unit
times the extension uniformizer raised to the ramification index. Since the
unit has shift zero, the base period is the product of the relative period
and the ramification index. [Uniformizer shifts](SubfieldLayerLifting.md)
