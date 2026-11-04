# Positive descent for an actual normalized subgroup

This derived unit connects an actual equivariant monomorphic inclusion to
integral Weyl averaging, Galois descent, and a specified split component. It uses
the canonical actions on actual character and cocharacter lattices. It does not
construct the geometric root system or the initial positive direction.

## Equivariance and the actual source

`AutomorphicAction.IsEquivariant.restrict` preserves equivariance when the acting
group is restricted along any homomorphism. `IsEquivariant.baseChange` preserves
it under any scheme base change. Both retain the equation on every test scheme.
The first proof substitutes the restricted acting point; the second applies the
actual base-change point equivalence and its composition and action identities.
The imported `IsEquivariant.isStable_range` from `Rational/FppfQuotientAction`
proves stability of the pointwise image subgroup: the source action supplies a
preimage of each transformed image point. These three lemmas require no field,
affineness, or monomorphism hypotheses.

Over any field in universe `u`, let `T` be a commutative group scheme, let `M`
be smooth, connected and affine, and let `U` and `G` be affine group schemes.
Fix actual homomorphisms `t : T.toGrp → M`, `j : M → G`, `i : U → G`, and an
action `d` of `M` on `U`. The underlying scheme map of `t` and the underlying
over-scheme map of `i` are monomorphisms. Assume `i` is equivariant from `d` to
conjugation along `j` on every test scheme.

`HasRelativeRootSystem.exists_centralCocharacter_positive_on_source` assumes
that `T` is split, that `t` has the published relative root-system realization,
and that a supplied integral cocharacter is strictly positive on every character
whose intrinsic weight space for `d.restrict t` is nonbottom. It produces an
integral cocharacter of `T`, central in `M`, strictly positive on exactly those
source characters. Centrality is the published all-test centrality of its actual
composite with `t`. The proof identifies source weight spaces with the ambient
support of `range i`, uses equivariance to establish normalization, applies the
integral Weyl averaging theorem, and returns through the same support comparison.
No arbitrary subgroup support-invariance premise is added.

## Galois support of the image

For any extension of fields `K/k`, an action of `T.toGrp` on an affine `U`, an
action of `T.toGrp` on an affine `G`, and an equivariant monomorphic inclusion
`i : U → G`, `RelativeRoot.mem_actionWeightSupport_range_galois_iff` preserves
and reflects the actual image support over `K` under every `k`-automorphism of
`K`. It uses the canonical character Galois action. The proof compares image
support with nonbottom source weight spaces, applies the individual descended
source weight-space transport theorem, and compares back. It requires neither
finite degree, Galoisness, splitness, nor a positive direction.

## Central descent and the specified split component

Return to the data `T,M,U,G,t,j,d,i` above. Now assume `T` is affine, `K/k` is a
finite Galois extension, and its automorphism group has a finite enumeration.
Write `T_K,t_K,d_K` for the actual base changes. Assume `T_K` is split, supply
`HasRelativeRootSystem t_K`, and supply an integral cocharacter of `T_K`
strictly positive on every nonbottom intrinsic weight space for
`d_K.restrict t_K`.

`exists_centralCocharacter_positive_on_descended_source` produces an integral
cocharacter of `T` over `k`, central in `M`, whose base change is strictly
positive on every original source weight over `K`. Smoothness, affineness, and
connectedness of `M` provide the corresponding properties over `K` through the
published geometric-connectedness theorem. Pullback preserves the required
monomorphisms and equivariance. The proof first makes the supplied direction
central by Weyl averaging over `K`. The canonical Galois action preserves the
nonbottom source weight spaces because both action and source descend. Integral
Galois averaging and all-test central descent therefore give the required
cocharacter over `k`. Both sums are unnormalized integral sums; no division or
characteristic assumption occurs.

Fix a commutative group scheme `A`, an actual specified split component
`a : A.toGrp → M`, a lift `f : A → T`, and the equality
`groupHom f ≫ t = a`. `IsSplitComponent.exists_positiveCocharacter_on_source`
produces an actual integral cocharacter `ζ` of `A` such that the base change of
`ζ ≫ f` pairs strictly positively with every original source weight over `K`.
The proof uses the published equality between the integral image of
`cocharacterMapInt f` and the central cocharacters of `t`; it requires no choice
of a different split component or lift.

`IsSplitComponent.positiveSourceCocharacter` chooses such an actual
cocharacter by classical choice. `positiveSourceCocharacter_spec` proves the
same strict positivity for this chosen value. No uniqueness or canonical-choice
claim is made. Empty source support is allowed and gives a vacuous positivity
condition.

`IsSplitComponent.sourceCharacterRestriction_ne_zero` proves that each
character with nonbottom source weight space has nonzero actual restriction
`f_K ≫ χ` on `A_K`. If the restriction were zero, functoriality of base change
and associativity of composition would make its integer pairing with the
extended image of `ζ` zero. This contradicts the strict positivity just proved.
The zero character here is the trivial homomorphism, not the zero value on one
rational point.

## Provenance and retained obligations

All results are derived from the published actual equivariance, tangent-weight
comparison, Weyl averaging, individual Galois weight-space transport, integral
central descent, and split-component range interfaces. Their proofs above
describe the implemented Lean route. This unit retains the relative root-system
realization, the splitting extension, the initial positive direction, the actual
action and equivariant inclusion, and the specified component and lift. It does
not infer these from parabolic minimality and does not prove
`MinimalParabolicLeviCentralizerStatement`, ambient maximal splitness, or the
radical and centralizer equalities of that target.
