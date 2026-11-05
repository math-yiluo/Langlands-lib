# Prescribed Borel curve data for the original rank-one cocharacter

This internal construction retains four structural hypotheses:
`SolvableProperFixedPointStatement`,
`ProjectiveTorusFixedPointDimensionStatement`,
`SolvableMaximalTorusConjugacyStatement`, and
`AlgClosedMaximalTorusCentralizerStatement`.
It does not supply proofs of those statements.

Over an algebraically closed field of arbitrary characteristic, fix a connected
reductive group, a split maximal torus embedding `i`, pairwise dependence of
its actual Lie roots, an actual root `α`, and a cocharacter `ν` pairing
nontrivially with `α`. Fix the prescribed Borel embedding `b` and its actual
torus factor `t`, with `t ≫ b = i`.

The helper
`IsConnectedReductive.centralizer_eq_torusCentralizer_of_rankOne` uses
`IsSplitTorus.isRegularCocharacter_of_rankOne` to make this original `ν`
generic on all roots. A split maximal torus is maximal among split tori, so
the proved `genericCentralizer` gives
`Z_G(ν ≫ i) = torusCentralizer i` on every test scheme.
This centralizer equality itself is proved over an arbitrary field;
algebraic closedness is used by the subsequent prescribed-Borel
construction.

`PrescribedBorelDynamicCurveData` extends the proper quotient data for
the specified `b`. It retains the actual quotient scheme and projection,
properness of that quotient, smoothness, surjectivity and quasi-compactness
of the projection, and its exact coset fibers on every scheme test.
The additional fields record that the quotient has topological Krull
dimension at most one, that `Z_G(ν ≫ i)` is contained in the range of `b`,
that the rational span of the actual roots has dimension exactly one,
and that `b` is not an isomorphism.

The construction `prescribedBorelDynamicCurveData` obtains maximal-torus
conjugacy in this Borel from the explicit conjugacy input. The explicit
self-centralizer input identifies the torus centralizer with the range
of `i`; the equation `t ≫ b = i` puts that range in the prescribed Borel.
The existing `prescribedBorelProjectiveCurveData` then supplies the proper
quotient and its dimension bound from the fixed-point inputs. The generic
centralizer equality supplies the original-cocharacter containment.
The published dependent-root span lemma gives exact rational rank one
using the actual nonzero root, and
`not_isIso_of_relativeRoot_of_isSolvable` gives properness of the
subgroup inclusion.

This is an internal deduction from the named Library results. The
geometric inputs remain explicit, and this construction alone is not a
proof of `RankOneBorelDynamicStatement`.
