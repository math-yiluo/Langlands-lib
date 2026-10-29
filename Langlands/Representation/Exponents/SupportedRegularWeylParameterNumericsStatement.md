# Numerical adapters for supported regular Weyl comparisons

Author: Worker 165.

`Langlands.Exponents.SupportedRegularWeylParameterNumericsStatement` is an
internal finite-coordinate statement for the supported regular comparison.
It has three clauses.

1. If a block shape has positive block sizes `d_i` and the size-weighted
   vector `d_i*v_i` lies in the closed positive root cone, the diagonal
   vector obtained by repeating `v_i` on its block also lies in that cone.
   The weights apply to the hypothesis; the conclusion uses actual
   diagonal coordinates.
2. For a coarse shape, a middle refinement, a further fine refinement, a
   direct fine refinement and a literal equality of the two fine shapes,
   the existing `IsPositiveRootParameter` implies that the transported
   repeated fine vector lies in the closed cone and is orthogonal to the
   repeated coarse real parameter. A strictly decreasing coarse parameter
   gives an antitone repeated diagonal vector. The statement retains the
   equality transport `h ▸ v` and arbitrary coarse central shifts.
3. Suppose two independent permutations `s` and `r` give the two oriented
   one-sided cone comparisons and fixed relations displayed in Lean.
   Assume each fine vector is orthogonal to its own coarse vector and
   both coarse vectors are antitone. If the original first fine vector
   also lies in the closed cone, then
   `V1 (s.symm i) = V2 i` for every coordinate and the inverse-transport
   vector `V2 (s i)` lies in the closed cone. The first permutation `s`
   is retained; no relation between the chosen permutations is assumed.

The provenance is internal algebra from the published block shapes,
coordinate maps, `RelativeRegularComparison.IsPositiveRootParameter` and
`Exponents.IsClosedPositiveRootCone`. The weighted parameter conversion
and zero-sum interfaces already appear in
`PositiveRootParameterConeStatement` and `PositiveRootBlockSumsStatement`.
This statement isolates the additional finite-coordinate work needed to
combine independent one-sided inputs. It does not state a representation
equivalence, select a Weyl witness, or assert Jacquet occurrence or
analytic continuation. Its third clause assumes the two one-sided
comparisons explicitly.

All ranks are permitted, including zero and the one-block case. The
statement has no field or representation carrier universes and uses no
representation-theoretic classification conclusion.
