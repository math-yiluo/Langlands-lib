# Dynamic induction normalization

This internal construction compares the Library's full-parabolic Haar-normalized
induction functor with induction obtained by twisting on the Levi and then
inflating along its actual projection. It is derived from published definitions
and proofs; it asserts no finite-length theorem and makes no comparison with an
external source's modular-function convention.

The generic `leviTwistedInductionFunctor` first applies the open-kernel Levi half
character, then `inflationFunctor`, then ordinary `smoothInductionFunctor`.
`normalizedInductionLeviTwistIso` constructs a natural isomorphism from the
existing full-parabolic normalized induction when the radical is unimodular.
The published `closedHalfCharacter_eq_comp_projection` identifies the two
characters, and `Langlands.twist_comp` identifies the inducing representations.
The identity linear equivalence on the inducing carrier gives a representation
isomorphism. Applying smooth induction gives its components; naturality follows
because all relevant maps act by postcomposition on functions.

For a connected reductive group scheme over any nonarchimedean local field,
`dynamicUnipotent_isUnimodular` applies
`BruhatTits.dynamicUnipotentCompactOpenContainment`, forgets openness with
`BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups`, and then applies
`General.isUnimodularModulus_of_isLimitOfCompactSubgroups`.
`dynamicClosedHalfCharacter_eq_comp_projection` specializes the resulting
character factorization. `dynamicNormalizedInductionLeviTwistIso` specializes the
generic natural isomorphism and discharges its unimodularity premise with that
proof.

The dynamic constructions use the canonical `rationalPointTopology`, with
local compactness and `NonarchimedeanGroup` on that exact topology and a supplied
proof that the actual radical is closed. These are exactly the typing hypotheses
of `DynamicInductionIrreducibleFiniteLengthStatement`. The field/group universe
`u` and input representation carrier universe `uV` remain independent; both
induction functors have output carrier universe `max u uV`. There is no
characteristic, splitness, admissibility, finite-dimensionality, irreducibility
or cuspidality hypothesis. The generic comparison separately takes its explicit
unimodularity premise; its dynamic specialization does not.

This is one normalization adapter for the finite-length proof. Actual-Levi
reductivity, standard-family comparisons, cuspidal embedding, transitivity, and
the finite-length argument remain separate obligations. The published target
and all its imports are unchanged.
