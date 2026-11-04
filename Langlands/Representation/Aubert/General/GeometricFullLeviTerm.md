# Actual geometric terms with full intersection Levis

Worker 167. This is an internal deduction from the published actual subgroup
and normalized representation constructions. It uses no additional assertion
from the literature.

For a locally compact nonarchimedean group `G`, let `P`, `M`, and `U` be subgroup
families indexed by finite subsets of an arbitrary type. The Levi and radical
families are closed. Fix subsets `I`, `J`, an element `n : G`, and the literal
source and target semidirect decompositions from `GeometricK0Target`. Suppose
that inverse conjugation by `n` identifies the two entire Levis:

`x ∈ M I ↔ n⁻¹ * x * n ∈ M J` for every `x : G`.

`geometricTermFullLeviIso` constructs, for every smooth complex representation
`A` of `M J` with carrier universe `max uG uV`, an isomorphism from the actual
normalized geometric term at `n` to `conjugationFunctor n hConj` applied to `A`.
Both index and carrier universes are independent of the ambient group universe.
The input is a literal subgroup conjugacy witness. No finite-length, cuspidality,
irreducibility, or functor-exactness premise is used.

The algebraic helpers `geometricSourceIntersection_eq_of_conjugation` and
`geometricTargetIntersection_eq_of_conjugation` show that the source intersection
is `M J` and the target intersection is `M I`. They use the definitions of the
intersections as subgroup infima with conjugated subgroup images, and the
membership criterion for the image of a group equivalence.

The published helper
`IsSemidirectDecomposition.unipotent_eq_bot_of_levi_eq_top`, imported from
`RationalFixedLeviComparisonProof`, shows that a semidirect decomposition with
full Levi has trivial radical. Its proof uses the disjointness of the Levi and
radical inside the parabolic: when the Levi is full, every radical element lies
in both and hence is the identity. Applied inside each coarse Levi, this gives
the trivial restricted radicals needed below.

`leviFullJacquetIso` handles the normalized Jacquet endpoint inside a closed
coarse Levi `M`. Its input decomposition has intersection Levi `L = M`; its
output is the original representation transported from `M` to the literally
named `L` by conjugation with `1`. The underlying linear equivalence is the
published `endpointCoinvariantsEquiv`. Its map takes a coinvariant class to its
vector, as expressed by `endpointCoinvariantsEquiv_mk`. The private character
helpers prove that the normalizer Haar modulus, its half character, and its
inverse half character are `1` on a trivial radical: the conjugation automorphism
of a subsingleton subgroup is the identity, whose Haar character is `1`.
Consequently the normalized action agrees with the original action. The final
identity-conjugation isomorphism retains the subgroup names in the type.

`leviFullInductionIso` handles the normalized induction endpoint for the same
kind of decomposition. The parabolic inside `M` is full because it contains
the full Levi. Its projection has the original underlying ambient element.
The half character is `1` by the preceding argument. The published
`Induction.smoothInducedTopEquiv` therefore identifies induction with the original
representation by evaluation at `1`. The result again uses identity conjugation
to retain the literal source and target subgroups. This construction requires
the saturated carrier universe `max uG uV`, as does the original induction
functor.

Finally, `geometricTermFullLeviIso` maps the source endpoint isomorphism through
the actual conjugation and target induction functors, composes with the target
endpoint isomorphism, and identifies the resulting three pullbacks with inverse
conjugation by `n`. The last linear equivalence is the identity on the original
carrier: both actions evaluate `A` at `n⁻¹ * x * n`.

This unit identifies a single actual geometric term. It does not construct a
normalized geometric filtration, prove a Jacquet equivalence for an induced
representation, or prove `RationalRankOneSelfAssociationStatement`. Rational
root-association and longest-representative specializations remain consumer
steps, using their existing actual subgroup-conjugation theorems.
