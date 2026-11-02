# Dynamic subgroup functors for an abstract automorphic multiplicative-group action

Let `S` be an arbitrary scheme, `G : GroupScheme S` an actual group scheme, and
`a : AutomorphicAction (Gm S).toGrp G` an action by group automorphisms.
This module constructs the subgroup functors `P`, `Z` and `U` for that action
on every scheme over `S`. All declarations are in
`Langlands.GroupScheme.AutomorphicAction`.

## Sources and scope

Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), §2.1
introduction, printed p.45 / PDF p.71, and Remark 2.1.11, printed p.59 /
PDF p.85, define the dynamic subgroups for abstract left actions by group
automorphisms. Lemma 2.1.5, printed pp.50–51 / PDF pp.76–77, gives the elementary
extension arguments for the subgroup and normalization laws. The registered
source is `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §2.11(a),
printed pp.130–132 / PDF pp.161–163, also permits an arbitrary automorphic
multiplicative-group action and uses extension to the affine line and the
value at zero. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered 2024 corrections, `kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp.24–26, correct notation in 2.11.1; they do not change these definitions.

The source definitions are expressed over affine bases using algebra points.
This module gives their intrinsic extension to arbitrary bases and all test
schemes. The single action morphism induces each orbit map by product
projections, and its naturality makes the construction commute with every
test restriction. Products, inverses and zero evaluation of actual extension
morphisms provide all the elementary proofs below. Thus the construction
includes nonaffine and nonreduced tests. It needs no affineness, separatedness,
smoothness or finite-presentation hypothesis on `G`.

The affine line, its zero section and its standard unit inclusion are exactly
the existing `AffineLine` constructions. Zero evaluation is the published
`Dynamic.evalZero`, used directly. The construction and elementary proofs
adapt the existing cocharacter `Dynamic.Basic` API to an abstract action.
The cocharacter comparisons are supplied by the separate
`Langlands.GroupScheme.Dynamic.ActionConjugation` module.

## Orbits, extensions and limits

For `g : T ⟶ G.X`, `orbit a g` is the morphism
`a.act (snd T (Gm S).X) (fst T (Gm S).X ≫ g)` from `T ×_S Gm` to `G`.
The action preserves the group structure in its second argument, so
`orbit_one`, `orbit_mul` and `orbit_inv` follow from `act_one`,
`act_mul_right` and `act_inv`. `whiskerRight_orbit` proves naturality in
`T` using the action naturality and product projection equations.

`IsOrbitExtension a g e` says that an actual morphism
`e : T ⊗ AffineLine.scheme S ⟶ G.X` restricts to `orbit a g` along
`T ◁ AffineLine.unitInclusion S`. The lemmas `IsOrbitExtension.one`,
`.mul`, `.inv` and `.whiskerRight` construct extensions by the corresponding
operations on the extension morphisms. Restriction uses the interchange law
for product maps and naturality of the orbit.

`HasLimit a g l` says that there exists such an extension `e` with
`Dynamic.evalZero e = l`. This is an existential predicate, with no chosen
extension or unique limit. `HasLimit.mul`, `.inv` and `.whiskerRight` use the
extension lemmas and the existing multiplication, inverse and naturality
lemmas for zero evaluation.

## Subgroup functors and elementary inclusions

`parabolic a` consists of points admitting an orbit extension;
`mem_parabolic` states this formula. The identity, product, inverse and
restriction constructions for extensions are exactly its subgroup-functor
laws.

`centralizer a` is defined to be `a.fixedSubgroup`, with its existing subgroup
laws and stability under all test restrictions. `mem_centralizer_iff_fixed`
states its all-refinement fixed-point condition. The universal fixed-point
test proves `mem_centralizer`: membership is equivalent to
`orbit a g = fst T (Gm S).X ≫ g`. Thus the centralizer is the invariant
subgroup functor; invariance only under `Gm(T)` is not substituted for it.

`unipotent a` consists of points having some orbit extension with identity
zero value; `mem_unipotent` exposes `HasLimit a g 1`. Multiplying or inverting
the extensions preserves the identity zero value. Pulling an extension back
along any test morphism also preserves it by naturality of zero evaluation.
These give all subgroup and restriction laws of this functor.

`HasLimit.mem_parabolic` forgets the zero-value condition.
`exists_hasLimit` evaluates an extension at zero to show that every point of
`parabolic a` has some limit. A centralizing point has the constant extension
`fst T (AffineLine.scheme S) ≫ g`; its restriction is its constant orbit
and its zero value is `g`. This proves `hasLimit_of_mem_centralizer`.
Consequently `centralizer_le_parabolic` and `unipotent_le_parabolic` give
`Z ≤ P` and `U ≤ P` on all tests.

## Normalization

For `p ∈ P(T)` and `u ∈ U(T)`, choose an orbit extension `e` of `p` and an
orbit extension `e'` of `u` with zero value `1`. The actual morphism
`e * e' * e⁻¹` extends the orbit of `p * u * p⁻¹` by the extension product
and inverse lemmas. Its zero value is
`Dynamic.evalZero e * 1 * (Dynamic.evalZero e)⁻¹ = 1`.
This is the implemented proof of `conj_mem_unipotent`.
`unipotent_isNormalizedBy_parabolic` packages it as
`a.unipotent.IsNormalizedBy a.parabolic`.

These declarations construct subgroup functors and their elementary laws.
They assert no representability, uniqueness of limits, equality of `Z` with
an intersection of opposite parabolics, quotient-action descent, semidirect
product group object, Lie-weight formula, open-cell theorem or relative
root-group existence.
