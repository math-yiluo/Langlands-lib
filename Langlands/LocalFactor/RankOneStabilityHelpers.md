# Helpers for rank-one stability

Worker 1786 derives these internal support results for the unchanged
`RankOneStabilityStatement`. Worker 784 is credited for the finite-level
duality implementation adapted from the published
`PadicAdditiveCharacterSelfDuality` pair. The proofs retain every prime,
arbitrary carrier universe, and supplied topological data.

Write `L_j = T.additiveLattice j`; this is the fractional ideal of elements
of normalized order at least `-j`, so the lattices increase with `j`.

`conductor_and_L` assumes `a = a(chi) >= 2` and `2*a(eta) <= a`. These
inequalities give `a(eta) < a`. The published different-conductor product
theorem therefore gives `a(chi*eta) = a`. Both characters are ramified, so
unfolding the actual constructors gives rational L factors equal to one
and their numerical representatives equal to one at every complex parameter.

`exists_parameter_lattice_character` concerns an additive character defined
only on `L_M`, trivial on `L_k` wherever that lattice meets its domain.
For every nontrivial continuous circle-valued additive character `psi`,
it supplies a field element `c` such that
`chi(x) = psi.complex(c*x)` throughout `L_M`.

Put `n = n(psi)`. The proof pairs the finite quotients
`L_M/(L_k intersect L_M)` and
`L_(n-k)/(L_(n-M) intersect L_(n-k))`. They are finite because an open
subgroup of a compact group has finite index. The annihilator theorem
makes the parameter-to-character map injective. Multiplication by
`uniformizer^(M+k-n)` identifies the relative indices, and finite
abelian character duality makes this injection surjective. The descended
given character therefore has a parameter. This adapts Worker 784's
published finite-level argument to a character on the lattice itself;
it uses no extension of that character to the whole field.
