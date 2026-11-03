# Rational coboundaries for linear vector actions of tori

This internal construction produces an actual rational coboundary point for a
torus acting scalar-linearly in supplied natural vector coordinates. Let `k` be
any field in universe `u`, let `H` and `V` be group schemes over `Spec k`, assume
`V` is affine over the base, and let `a` be an actual automorphic action of `H`
on `V`. The input `e` identifies `V(T)` with the additive group of
`Fin d → Γ(T, ⊤)` on every relative test scheme, naturally in `T`.
`IsLinearVectorCoordinates a e` additionally requires the original action to
commute with every scalar in that ring of global sections. These coordinate
data and their laws are supplied, not constructed here.

For every `IsTorus H` and every actual base-parametrized cocycle `c`,
`torusCocycleConjugator` chooses a section `v : Spec k → V` from the proved
existence result. `cocycle_eq_coboundary_of_isTorus` proves
`c = a.coboundary v` as actual cocycles. The convention is
`c(h) = v * a(h, v⁻¹)`, so its additive coordinate version is
`c(h) = x - a(h)x`. Equality of cocycles implies the formula on all relative
tests, including non-affine tests.

The first transport lemmas show that restricting the acting group preserves
actual coboundaries and that restriction along an actual group-scheme
isomorphism is injective on cocycles. Thus
`exists_coboundary_of_isSplitTorus` transports the constant Laurent coefficient
construction from `Rational.SplitTorusVectorCocycle` along the isomorphism in
`IsSplitTorus`. `exists_splitting_coboundary` then uses the splitting field in
`IsTorus` and the action, cocycle and coordinate base-change constructions.
Neither transport requires the torus to have been presented in split coordinates
over the original field.

The rational descent is elementary linear algebra. `fieldRetraction k K` is a
`k`-linear left inverse of the scalar inclusion `k → K`, obtained from the
injectivity of that linear map. In particular it sends `1` to `1`. For every
commutative `k`-algebra `A`, `contract k K A` contracts the second tensor factor
of `A ⊗[k] K`. It is `A`-linear and satisfies

`contract(a ⊗ z) = algebraMap k A (fieldRetraction k K z) * a`.

It fixes the inclusion of `A` and contracts the inclusion of `K` by the displayed
formula. `contract_mulVec` proves compatibility with every finite matrix whose
coefficients come from `A`. `coordinateAction_contract` applies this to the
actual action's finite Lie coordinate matrices, using their naturality under
the inclusion of `A`. The existing scalar-linearity theorem identifies this
differential action with the original vector action.

The affine base-change comparison intertwines cocycle evaluation and the actual
action. `vectorAffineCoordinates_basePoint` identifies the coordinates of a
constant section with scalar extension of its rational coordinates. These facts
give `cocycleCoordinates_of_baseChange_coboundary`: a primitive over `K` gives the
original coordinate coboundary formula on every compatible `K`-algebra.

To recover the equation on an arbitrary original test algebra `A`,
`cocycleCoordinates_contract` applies that formula over `A ⊗[k] K`, viewed as a
`K`-algebra through the right tensor factor, at the image of the original acting
point through the left factor. Naturality identifies the left side with the
inclusion of the original cocycle coordinates. Applying `contract`
coordinatewise fixes that side and commutes with the action. The primitive vector
becomes the scalar extension to `A` of the coordinatewise contraction of its
`K`-rational vector.

`exists_coboundary_of_baseChange` turns this contracted vector into an actual
`k`-section by the inverse vector-coordinate equivalence on the affine base
test and the affine self-test isomorphism. Its scalar-extended coordinates give
the coboundary identity on every affine algebra. Affineness of the acting group
then gives equality of the actual cocycle morphisms. Finally,
`exists_coboundary_of_isTorus` obtains affineness from `IsTorus`, applies the
splitting-field construction and descends its primitive.

This is a derived internal contribution: all arguments use the existing actual
cocycle, vector-coordinate, finite-action and base-change interfaces and ordinary
linear algebra; no external vanishing or descent theorem is assumed.
The construction permits arbitrary characteristics, finite and imperfect base
fields, nonsplit tori and dimension zero. The extension used for descent can be
arbitrary: no finiteness, separability, Galois structure or division by its degree
is needed. It does not prove that a given torus action admits these coordinates,
construct a vector subgroup in a solvable group, or prove the full maximal-torus
conjugacy statement. Those remain separate obligations of the host task.
