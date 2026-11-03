# All-test opposite-cell reduction for normalizer separation

This internal reduction implements the normalizer-intersection step of
Borel–Tits, *Groupes réductifs* (1965), §5.15, equation (2) and its proof,
printed page 100 (zero-based PDF page 46, one-based page 47). The result is
conditional on injectivity of opposite-cell multiplication on every test
scheme. The source obtains this input from its opposite-cell isomorphism.
For an affine ambient group, the final corollary discharges this
injectivity condition using the published opposite-intersection theorem.
The Lean proof uses the Library's actual dynamic subgroup functors, actual
normalizer points, and unique orbit-extension limits.

Write `χ = CommGroupScheme.groupHom ν ≫ i` and
`χminus = CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ`. The latter
is the inverse cocharacter used in the published `OppositeCellStatement`.
Let `U`, `Uminus` and `P` denote the dynamic unipotent, opposite-unipotent
and parabolic subgroup functors for these cocharacters.

`HasInjectiveOppositeCellMultiplication i ν` says that for every test
scheme `X` over the field, multiplication from
`Uminus(X) × P(X)` to `G(X)` is injective. It is an internal interface,
not an assertion of the geometric opposite-cell theorem.

The file provides four conditional adapters for this interface.
`hasInjectiveOppositeCellMultiplication_of_trivial_intersection` uses the
explicit condition that a point in both `Uminus(X)` and `P(X)` is the
identity, on every test. Given equal products, the quotient of the two
first factors also equals the quotient of the second factors, hence lies
in this intersection. Its triviality gives equality of both factors.
`hasInjectiveOppositeCellMultiplication_of_inf_eq_bot` expresses the same
input as an equality of subgroup functors.

`hasInjectiveOppositeCellMultiplication_of_mono` takes homomorphisms
representing `Uminus` and `P` and a monomorphism assumption on their
multiplication map. The range identities in representability lift both
pairs of points to the representing product. Cancellation of the
monomorphism makes the lifts equal, and projection recovers the two
original factors. The open-immersion version obtains this monomorphism
from the underlying scheme open immersion. These adapters impose no
affineness or smoothness assumption of their own and do not prove an
open immersion or the trivial-intersection input.

`hasInjectiveOppositeCellMultiplication_of_isAffine` supplies the
injectivity predicate for every cocharacter whenever the ambient group
has affine underlying scheme. It applies the preceding intersection
adapter to `Dynamic.opposite_unipotent_inf_parabolic`. The opposite
cocharacter in that theorem is definitionally the inverse-power
composition used here. This argument uses an equality of subgroup
functors and therefore supplies injectivity on arbitrary test schemes.

For an affine group scheme,
`commute_unipotent_factors_of_normalizer_of_injectiveOppositeCell` proves
that if `n = v * u` with `n` normalizing `i`, `v ∈ Uminus(k)` and
`u ∈ U(k)`, then the base changes of `v` and `u` commute with every point
of the commutative group scheme mapped by `i`, over every test scheme.
The proof proceeds as follows.

For `t ∈ T(X)`, put `s = i(t)` and `s' = i(σ(t))`, where `σ` is the
automorphism induced by `n`. Normalization gives `n s n⁻¹ = s'`.
The helper `range_le_torusCentralizer` shows that both `s` and `s'`
centralize the cocharacter; it uses commutativity on every refinement of
`X`. The helper `SubgroupFunctor.constantPoint_mem` transports the
unipotent memberships of the two base points to `X`.

The pairs `(v,u)` and `(s' v s'⁻¹, s' u s⁻¹)` belong to
`Uminus(X) × P(X)` and have the same product. Opposite-cell injectivity
therefore gives
`s' v s'⁻¹ = v` and `s' u s⁻¹ = u`. The limit of the latter left-hand
side is `s' s⁻¹`, since the centralizing factors have constant limits and
`u` has limit the identity. Its equality with `u` and uniqueness of limits
give `s' s⁻¹ = 1`, hence `s' = s`. Both conjugation equations now say
that the factors commute with `s`.

`normalizer_eq_one_of_injectiveOppositeCell` concludes that `n = 1`.
The all-test commutation just proved places each factor in the centralizer
of the whole mapped commutative group scheme at the base. Each factor
therefore lies in the dynamic centralizer for its own cocharacter as well
as in the corresponding dynamic unipotent subgroup. Unique limits imply
that both factors are the identity, and `n = v * u` finishes the proof.

`normalizer_eq_one_of_unipotent_product` supplies the proved
injectivity input to that theorem. In an affine ambient group, a
normalizing rational point that is the product of an opposite-unipotent
point and an original-unipotent point is consequently the identity,
without an additional geometric assumption.

These results hold over an arbitrary field and universe `u`, with any
commutative group scheme `T` and any homomorphism `i`. Affineness of `G`
supplies separatedness and uniqueness of limits in the normalizer
arguments and the opposite-intersection result in the affine corollaries.
No connectedness, reductivity, splitness, maximality, or genericity is
assumed in these results. Rational
torus-point commutation is never used as a substitute for whole-group
centralization. In the affine case the injectivity input is discharged.
Weyl factorization and covering remain obligations for the unchanged
exact `RationalBruhatStatement`.

The all-test self-centralizing range lemma `range_le_torusCentralizer` is
reused from `LeviFactorization`.

The affine corollaries have internal provenance: they compose the
published coordinate proof of the opposite dynamic intersection with
the group-algebra injectivity adapter and the normalizer argument
described above. They do not assert an opposite-cell open immersion.
