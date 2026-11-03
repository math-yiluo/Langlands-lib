# Discrete and closed actual function-field diagonals

`Langlands.Global.FunctionFieldAdelesDiscreteStatement` is a derived
proposition target about the published full-field diagonals and actual
restricted-product topologies. All fields in each clause lie in one arbitrary
universe, with compatible `k`- and `RatFunc k`-algebra structures and
`FunctionField k F` (finite dimensionality over `RatFunc k`).

The first clause assumes `PerfectField k`. It states that the subring image
of `curvePlaceAdeleDiagonal k F` has discrete subspace topology and is closed
in `CurvePlaceAdeleRing k F`. This ring is the cofinite restricted product of
the actual adic completions at all actual curve places, relative to their
completed valuation rings. Perfectness is retained from the published
finite-poles construction of the full-field diagonal. No finite-cardinality
hypothesis on `k`, separability of the given rational-function presentation,
finite-residue hypothesis, or compactness hypothesis is imposed.

The second clause assumes `Finite k`. It states the same conclusions for the
subring image of `realAbsoluteValueAdeleDiagonal k F` in
`RealAbsoluteValueAdeleRing k F`. Its indices form the actual quotient of all
nontrivial real absolute values by equivalence, its factors are the actual
absolute-value completions of chosen representatives, and its integral
subrings are their norm unit balls. The topology is the published cofinite
restricted-product topology. The image has its existing subspace topology.
Finite fields are perfect; no additional perfectness input is needed here.

This is implementation-level arithmetic and topological infrastructure for
the function-field branch of the Conrad program, rather than a numbered
assertion transcribed from the paper. The valuative characterization of
integral closure shows that an element integral at every actual curve place
is algebraic over `k`. A valuation trivial on `k` takes value one on every
nonzero algebraic element. Thus the open set of adeles integral at all places
and of valuation strictly below one at one reference place isolates zero in
the diagonal. Translation gives discreteness; the Hausdorff topological-group
criterion gives closedness. The published diagonal-preserving adelic
homeomorphism gives the absolute-value version.

This unit declares the target and contains no proof. It does not claim a
compact adelic quotient, model descent, or a geometric point-space comparison;
those and the remaining whole-paper assertions remain separate obligations.
