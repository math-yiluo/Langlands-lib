# Coarse scalar action on actual inner induction

Author: Worker 526. The namespace is
`Langlands.InnerInducedCoarseScalar`. These internal adapters use the
published induced-function construction and the nested scalar-character
proof of Workers 526, 359 and 438.

`scalarAction` takes a fine representation of the actual refined Levi
and a coarse tuple character acting along repeated coarse block scalars.
The same character acts by scalars on the actual normalized inner
induction. No admissibility, irreducibility or nonvanishing hypothesis
is needed for this calculation.

Evaluate the induced functions at each group element. Right translation
by a coarse block scalar equals left translation because it is central.
`flattenedLeviEquiv_blockScalarLevi_comp` identifies the repeated fine
scalar with this actual coarse element. Its section lies in the refined
parabolic and projects back to the original element. Defining covariance
therefore applies. `refinedLeviHalfModulus_blockScalarLevi_comp` makes the
positive half modulus one; the given scalar equation finishes the proof.
The actual function carrier and normalization are retained.

`realBlockEqTopOfScalar` takes an exact coarse scalar character on a
smooth representation. Transporting it to the full centre by
`blockScalarCenterEquiv` yields the same real part on restriction. For a
nontrivial carrier, the scalar action and smoothness give an open
character kernel. For a subsingleton carrier every vector is zero.
The published scalar-to-grouped-space lemma then identifies the entire
carrier with its real central block. No continuity of the inverse
centre equivalence is assumed.

`nestedScalarCharacter` applies
`Exponents.coarseFineTwistScalarCharacter` across the fixed nested
flattening equality. It preserves its irreducibility, admissibility,
unitarizability and positive-root hypotheses. For every coarse vector
`t`, the induced scalar character has open kernel and real coordinates
`size i * t i`. `nestedRealBlockEqTop` applies the preceding full-centre
argument to the smooth actual inner induction. It allows a zero induced
carrier and retains independent field and fine-carrier universes.
