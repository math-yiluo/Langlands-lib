# Transport of the actual universal Picard-zero property

`Langlands.AbelianScheme.picardZeroUniversalBaseChange.{u}` proves the
published `PicardZeroUniversalBaseChangeStatement.{u}`. Given an actual
universal rigidified Picard-zero family `L` for `A/S`, it proves that
`(baseChangeFamily b A P).obj L` is universal for the actual base change
of `A` along any morphism `b : S' → S`.

This is an internal derived consequence of the existing universal
property and the published comparisons of actual scheme and line-bundle
pullbacks. Its provenance is the intrinsic transport obligation described
in the target's Markdown. The proof works directly with the Library's
geometric translation-invariance predicate and asserts no additional
identification with a literature definition of Picard zero.

The private lemma `universalBaseChange_of_geometric` rewrites
universality using `isUniversalPicardZero_iff`: the family is Picard-zero,
and every Picard-zero family is isomorphic to its pullback along a unique
parameter map. The explicit new family is a parameter pullback followed
by ground-base pullback. The first operation preserves Picard-zero by
`picardZeroPullback`, and `picardZeroFamilyBaseChange` supplies preservation
and reflection for the second.

For any test scheme `T/S'` and Picard-zero rigidified family `M`, let `N`
be its image under `familyBaseChangeInverse`. The counit identifies the
forward pullback of `N` with `M`. Invariance under isomorphism and
reflection of Picard-zero therefore show that `N` is Picard-zero.
Universality of `L` gives a unique map `g : T → P` over `S` and an
isomorphism from its parameter pullback to `N`.

The slice pullback adjunction, implemented by `baseChangeParameterEquiv`,
transposes `g` to a map `T → P_{S'}` over `S'`.
`baseChangeFamilyPullbackIso` identifies pullback of the explicit new
family along that map with ground-base pullback of the old classified
family. Composing with the image of the classifying isomorphism and the
counit produces the required isomorphism to `M`.

For another classifying map, the same compatibility followed by the
inverse family functor and the inverse unit gives a classification of
`N` over `S`. Old uniqueness identifies its transpose with `g`;
injectivity of `baseChangeParameterEquiv` gives uniqueness over `S'`.
The final theorem instantiates the private lemma with the published
`picardZeroFamilyBaseChange`. All schemes lie in one universe, and every
test scheme is allowed, including nonreduced schemes. The theorem
transports a supplied universal family and proves no existence theorem
for dual abelian schemes.
