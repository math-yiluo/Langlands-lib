# Epimorphisms and projective lifting in the actual inertia block

Worker 1740 constructs categorical lifts inside the actual full subcategory
`RationalInertiaBlock G π`. This is an internal consequence of the published
all-irreducible-subquotients definition and its closure under actual
subquotients. It is a categorical helper for the small-progenerator theorem,
with independent field and representation-carrier universes. The base `π`
need not be irreducible or cuspidal.

The actual block contains zero: a subquotient of a representation with a
subsingleton carrier again has a subsingleton carrier, which contradicts
irreducibility. The published theorem
`Langlands.CuspidalSupport.subsingleton_of_isSubquotient` from
`JacquetVanishingHelpers` supplies this fact for arbitrary commutative coefficients. The helper
`SmoothRep.subsingleton_of_isZero` uses the equality of the identity and
zero endomorphism of a categorical zero object.

The block property is closed under categorical subobjects and quotients.
Indeed, monomorphisms and epimorphisms of smooth representations are
respectively injective and surjective, and therefore give actual
subquotients. The published block-closure theorem applies. Mathlib's
full-subcategory results then show that its inclusion preserves
monomorphisms and epimorphisms.

Consequently, `rationalInertiaBlock_epi_iff_surjective` identifies a block
epimorphism with a surjective underlying intertwiner, and
`rationalInertiaBlock_mono_iff_injective` gives the corresponding statement
for monomorphisms. No category decomposition, finite length or additional
assumption of abelianness of the block is used.

For a block object `P` whose underlying smooth object is projective,
`rationalInertiaBlockProjectiveLift G π P f q` chooses an ambient projective
lift and bundles it as a morphism of the full block.
`rationalInertiaBlockProjectiveLift_comp` proves that it composes with `q`
to `f`. Finally, `rationalInertiaBlock_projective_of_projective` gives
categorical projectivity of `P` inside the block. This result takes ambient
projectivity as a premise; it does not claim projectivity or membership of
the particular norm-kernel compact induction.

All mathematics is derived from the imported Library modules
`CuspidalSupport.RationalInertia`, `CuspidalSupport.JacquetVanishingHelpers`,
`Representation.Category.Abelian`, and
Mathlib's projective and full-subcategory infrastructure. No additional
literature assertion is introduced.
