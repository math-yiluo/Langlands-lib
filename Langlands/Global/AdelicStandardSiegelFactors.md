# Canonical standard subgroup schemes in actual adelic factor products

This internal construction connects the existing actual adelic factor products
to the Library's concrete closed representatives of the standard subgroup
functors. It applies over every number field F to any affine group scheme G,
any commutative group scheme T with an actual morphism i : T → G, and any
cocharacter ν of T. It imposes no reductivity, splitness, maximality or genericity
assumption.

`canonicalStandardFactors` fills every field of the existing
`AdelicSiegelFactors.StandardFactorData F G T i ν` using
`Standard.unipotentScheme i ν ∅` and `Standard.leviScheme i ν ∅`, their actual
inclusions, and their proved closedness and all-test representability. A
consumer may therefore form `CompactFactors` and the actual adelic
`productSet`, `weakSiegelProduct` or `strictSiegelProduct` for these specific
group schemes without supplying new representing groups or witnesses.
The construction chooses no compact subsets.

`torusToStandardLevi` is an actual group-scheme morphism from T to the
represented standard Levi. Its composite with the Levi inclusion is i.
The proof uses that a commutative group's image centralizes itself on every
test scheme, that this torus centralizer lies in every standard Levi, and
the existing Yoneda factorization through a represented subgroup.
`torusToStandardParabolic` composes with `Standard.leviToParabolic`; its
composite with the parabolic inclusion is again i. These are factorizations
of the given morphism, without an assertion that it is injective.

`standardParabolic_adelic_range` identifies the image of the actual
continuous adelic-point map from `Standard.parabolicScheme i ν ∅`
with the shared `standardParabolic i ν ∅` subgroup evaluated on the
actual adele algebra. This follows by evaluating the all-test
representability equality at that affine test scheme. Thus the statement
compares the actual represented group's points with the actual standard
subgroup; it introduces no replacement point model.

Given any actual commutative morphism j : T₀ → T,
`positiveMap_mem_standardLevi` proves that the image of each point in
`PositiveRealTorus.intrinsicSubgroup F T₀` belongs to the shared standard
Levi functor on the adelic test algebra. Its proof explicitly writes that
image as the i-image of the j-image of the original point, then uses the
all-test torus-centralizer containment. No split-torus identification or
norm-one assertion is used in this step.

`productSet_subset_standardParabolic_mul_compact` applies to every existing
`StandardFactorData D` and `CompactFactors C`, including the concrete
`canonicalStandardFactors`. For every subset A of the intrinsic positive
torus it proves

ΩN ΩM A K ⊆ image(Standard.parabolicScheme(A_F) → G(A_F)) K,

with all maps and products taken in the existing adelic group and with
the compact factor on the right. The proof first puts the N-image in
the standard unipotent functor and the M-image in the standard Levi
functor using D's representation fields. Both functors lie in the
standard parabolic. The preceding positive-point lemma puts the A-image
there too. Multiplication in that subgroup then puts the three-factor
prefix in it. The exact range equality supplies an actual parabolic
adelic point mapping to the prefix, which gives the displayed containment
with the same K. The theorem neither uses nor asserts an Iwasawa
decomposition.

The provenance is the published `AdelicSiegelFactors`,
`GroupScheme.Rational.StandardRepresentability` and
`GroupScheme.Rational.LeviFactorization` constructions, together with the
existing all-test standard subgroup inclusions. No external structural
theorem is added. In particular, as in `StandardRepresentability`, these
named standard schemes represent the existing choice-free intersections
even when the family of standard cocharacters is empty. The module does
not prove that its named parabolic is a minimal rational parabolic, that
its named unipotent scheme is a unipotent radical, or that its named Levi
is connected reductive. Those identifications require the corresponding
algebraic structural results.

The containment proves neither covering by the parabolic product nor
rational saturation of a Siegel set. Derived maximal split tori, the
central complement, maximal compact existence, reduction coverage,
finite volume and height independence remain separate obligations.
