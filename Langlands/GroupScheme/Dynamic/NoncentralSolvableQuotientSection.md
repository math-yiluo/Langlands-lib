# Nonfixed quotient sections from a noncentral smooth connected subgroup

This internal normal-closure argument works over any algebraically closed field
`k : Type u`, in any characteristic. It keeps
`AlgClosedReductiveNormalSolvableTorusStatement` as an explicit structural input.
Let `G` be pseudo-reductive in the Library's sense, let `i : H → G` have smooth,
connected affine source, and let `j : P → G` be a closed solvable subgroup.
Let `q : G → Q` be flat, surjective and quasi-compact, with fibers on every
relative scheme test equal to the right cosets of the range of `j`.

`Dynamic.isCentral_of_all_quotientLifts_fixed_of_structural` proves that `i` is
central if every rational lifted quotient section is fixed, on all tests, by
the quotient action restricted to `H`. For a rational pair `(g,t)` of `G × H`,
fixedness of the quotient of `g⁻¹` puts `g i(t) g⁻¹` in `P` using the exact
fiber law. The product is smooth, hence reduced and locally of finite type.
`UnipotentAllBorelsEnvelope.exists_factor_of_algClosed_points` therefore factors
the actual conjugation morphism through the closed subgroup `P`.

The published `smoothConnectedNormalClosure` of `i` consequently factors through
`P` by its minimality. This factor is a closed inclusion, so the normal closure
is solvable. It is smooth, connected, and normal by construction. The supplied
structural input makes its inclusion central. Containment of the original image
in this normal closure proves centrality of `i` on every scheme test.

`Dynamic.nonfixedQuotientLiftOfNoncentralSubgroup_of_structural` takes
noncentrality of `i` and selects an actual rational point `g` whose quotient
section is not fixed, using the contrapositive of that theorem.

The provenance is internal derivation from the named Library constructions.
The argument requires no properness or separatedness of `Q`, no torus
conjugacy, no centralizer containment, and no Weyl finiteness. It does retain the
normal-solvable-torus statement as a theorem-valued premise, and does not prove
the unconditional positive-root uniqueness statement.
