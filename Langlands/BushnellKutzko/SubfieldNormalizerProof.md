# The normalizing subfield criterion

`Langlands.BushnellKutzko.subfieldNormalizer` proves
`SubfieldNormalizerStatement` in independent universes for the base
field, vector space, and acting field. The target is Bushnell and
Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), Proposition (1.2.1), printed pp. 24–25 (PDF pp. 36–37).
The source is registered as `bushnell-kutzko-1993-admissible-dual-gln`.
[Published statement](SubfieldNormalizerStatement.md)

The chain gives a nonzero finite-dimensional \(F\)-vector space.
Evaluation at a nonzero vector embeds \(E\) in this space, giving
`LatticeChain.finiteDimensional_subfield`. The finite extension
arithmetic makes its integral closure \(\mathfrak o_E\) a discrete
valuation ring with fraction field \(E\). Choose a uniformizer
\(\pi\), which generates the ideal `subfieldMaximalIdeal F E`.
[Integral closure arithmetic](SubfieldIntegerArithmetic.md)

For any \(\mathfrak o_E\)-stable lattice, the \(\mathfrak o_F\)-span
of the maximal-ideal scalar products equals the image under
multiplication by \(\pi\). Each generator \((\pi b)x\) is the image
of \(bx\), which is still in the lattice. Each vector \(\pi x\)
already belongs to the generating set.

If \(E^\times\) stabilizes the chain, the monic relation of any
nonzero integral scalar gives a nonnegative shift, by
`LatticeChain.fieldShift_nonneg_of_integral`. This proves lattice
stability via `LatticeChain.subfieldInteger_smul_mem`. The action of
\(\pi\) has a single shift \(d\) by `LatticeChain.exists_shift`, so
the maximal-ideal span of \(L_i\) is \(L_{i+d}\).
[Lattice chain shifts](LatticeChainShifts.md)

Conversely, lattice stability and the span equality imply that
\(\pi\) shifts the chain as prescribed. A ring unit \(u\) fixes each
lattice because both \(u\) and \(u^{-1}\) preserve it. Every field unit
is a product of such a unit and an integer power of \(\pi\) by
`subfieldUnit_factorization`. Closure of the stabilizer under
products and integer powers gives the conclusion.
[Unit factorization](SubfieldValuationShifts.md)
