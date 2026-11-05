# Compact coefficients and escaping Iwahori contractions

Worker 389 derives two abstract helpers for the compact-restriction converse.
They concern an arbitrary topological group, independent group and vector-space
universes, an arbitrary smooth complex representation, and an actual subgroup
with its induced topology. No admissibility or dimension premise is used.

`HasEscapingPowers g` means that the nonnegative powers of `g` eventually
leave every compact subset of the ambient topological group. Both helpers
below take this property as an explicit premise.

`mem_relations_of_compactCoefficients_of_iwahoriContraction` takes a compact open
subgroup `K`, an actual Iwahori contraction for `(N,M,Nbar,g)`, normalization of
`N` by `M`, membership of `g` in the coefficient subgroup `H`, and eventual escape
of the powers of `g` from every ambient compact subset. It proves that every
`K`-fixed vector belongs to the actual relation space `Jacquet.relations ρ N`.

For each algebraic functional, precomposition with the compact averaging map
produces a functional smooth on the restricted action. Compact support of that
coefficient and escape of `g^n` imply eventual scalar vanishing of the averaged
vectors. The published algebraic dual lemma in `HarishChandraConverseProof`
then gives an averaged vector equal to zero. The published abstract power-kernel
identity from `IwahoriContractionAdmissibility` puts the original vector in the
kernel of the genuine Jacquet quotient map. The proof uses its generalized
kernel statement, which requires no finite-dimensional fixed space.

`relations_eq_top_of_compactCoefficients_of_iwahoriBasis` additionally takes an
ambient-cofinal basis of such compact open subgroups for the same element `g`.
It chooses one fixing each vector and applies the preceding result. Its
conclusion is that the entire actual relation submodule is top.

This is derived internal content from the named published averaging, algebraic
dual and Iwahori contraction results. It does not construct a contracting element,
prove norm-kernel membership or escape, or supply a reductive-group basis.
The exact general rational-point converse remains a separate assembly obligation.
