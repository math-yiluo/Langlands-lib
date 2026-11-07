# Actual smooth-dual base factors for a unitary supercuspidal family

This internal adapter starts from original irreducible unitarizable
supercuspidal actions, with arbitrary positive ranks, canonical p-adic
topology, a supplied unitary additive character, and its self-dual Haar
measure. The equal-rank supercuspidal factor formula is an explicit premise.
The field and two action carriers have independent universe parameters.

`unitarySupercuspidalDualPairEuler` applies the arbitrary-rank Euler
constructor to the first original action and the actual smooth
contragredient of the second. The published supercuspidal contragredient
proof supplies supercuspidality and irreducibility of that dual.
Compact-open cofinality and the admissible invariant-form construction
supply unitarity of the dual. These properties are proved inputs, not
additional duality hypotheses.

`isRankContragredient_dual_of_equiv` composes a supplied equivalence of
original actions, including its rank transport, with the actual smooth
bidual evaluation equivalence. Admissible smooth duality proves evaluation
is bijective. Thus the exact parameter-one test in the Euler datum holds
whenever the original actions match.

`unitarySupercuspidalBaseFamily` applies this construction to any dependent
family of positive ranks and action carriers in one common carrier
universe; the index universe is independent. Every pair retains its actual
symmetric polynomial certificate and residue cardinality. Consequently,
`SupercuspidalPairEuler.reciprocal_eq_of_certified` identifies each base
function with the spectral reciprocal of every certified symmetric pair
polynomial for the original action and actual smooth dual.

For a supplied partner function, equal ranks and equivalences of the
original actions suffice for `unitarySupercuspidalBaseFamily_conditions`.
The implemented proof uses smooth bidual evaluation to obtain the
parameter one in every matched pair, then applies the finite unitary Euler
analysis. This proves all `BasePairConditions`: meromorphy and finite
nonpositive order at real points, holomorphic nonzero values at positive
real points, and strict negative order at zero for every matched pair.
No finiteness or involutivity of the partner is needed for this analytic
step.

The provenance is composition of proved Library duality and finite Euler
results. This module does not prove the retained equal-rank formula, a
segment formula, or the associated-pair induction theorem.
