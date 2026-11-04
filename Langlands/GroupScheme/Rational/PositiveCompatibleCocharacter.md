# Compatible whole-torus centralizers preserving finite positivity

This derived unit refines the published
`Rational/CompatibleTorusCocharacter` construction by preserving positivity on
a supplied finite family of integral additive forms. Its proof adapts that
module's dominant-combination argument and adds the integral bound from
`Absolute/RegularPerturbation`. It makes no new literature assertion.

Let `k` be any field in universe `u`, let `B` be a commutative group scheme
which is a split torus, and let `G` be affine and locally of finite type over
`k`. Fix a group-scheme homomorphism `b : B.toGrp → G`, an actual integral
cocharacter `ν : Gm → B`, and a finite family of additive maps from the
cocharacter lattice of `B` to `ℤ`. The family is specified by an index type
`I` in an independent universe `v`, a function `q` assigning an additive map
to each index, and a finite set `s` of indices. Neither monicity of `b` nor
reductivity of `G` is assumed.

`IsSplitTorus.exists_compatible_cocharacter_on_finite` produces an actual
cocharacter `ζ` of the same specified torus `B` with four properties:

1. Its ambient dynamic centralizer is the whole-torus centralizer of `b`.
2. Its dynamic parabolic is contained in that of `ν`.
3. Its dynamic identity-limit subgroup contains that of `ν`.
4. For each index in `s`, strict positivity of its form on `ν` implies
   strict positivity on `ζ`.

The equality and inclusions are equalities and inclusions of subgroup
functors on every test scheme. The finite-family assertion only preserves
strictly positive values. It asserts no sign preservation for forms whose
original value is zero or negative. Empty finite families are allowed.

Choose the published whole-torus centralizing cocharacter `τ`. Commutativity
of `B` places its image inside the dynamic centralizer of `ν`, so
`Dynamic.exists_dominant_inclusions` supplies a threshold for the combination
`Nν + τ`. Take `N` to be the maximum of this threshold and
`IntegralPerturbation.bound q s τ`. The first bound supplies the two dynamic
inclusions and containment of the new centralizer in the old one. An element
centralizing the combination and `ν` also centralizes their difference `τ`;
the defining property of `τ` then gives the whole-torus centralizer equality.
The second bound gives the lexicographic sign formula for each selected
integral form, so each form originally positive on `ν` remains positive.
All combinations are integral and no division occurs.

`compatibleCentralizingCocharacterOnFinite` chooses this actual cocharacter
by classical choice. Its `_spec` theorem proves the four stated properties
for the chosen value. No uniqueness or canonical-choice assertion is made.

In the Levi-centralizer application, the forms can be pairings of source
characters after base change and postcomposition with a specified lift.
That application still has to supply these additive forms, their finite
index family, and an initial cocharacter positive on them. This unit does
not construct the initial positive direction, a relative root system, a
splitting extension, ambient maximal splitness, or a factorization through a
specified geometric solvable radical, and does not prove
`MinimalParabolicLeviCentralizerStatement`.
