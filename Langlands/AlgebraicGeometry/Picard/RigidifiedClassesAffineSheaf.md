# Conditional affine flat sheaf condition for rigidified classes

For an arbitrary scheme morphism with a section, this internal result assumes
ordinary line-bundle isomorphism descent, ordinary effective line-bundle
descent, and uniqueness of relative rigidified isomorphisms over all test
schemes. It proves the singleton sheaf condition for the actual presheaf of
rigidified line-bundle classes along every affine flat surjective slice
morphism.

`affineFlatAmalgamation` chooses the global relative rigidified line bundle
provided by conditional effective descent for compatible local data.
`affineFlatAmalgamation_pullback` proves that its pullback is isomorphic to
the original local relative rigidified line bundle. This choice uses ordinary
effective descent and rigidified isomorphism uniqueness; it does not require
the separate isomorphism-descent assumption used for separation below.

The singleton criterion expresses compatibility as equality of the two
pullbacks along every pair of slice maps with equal composite. On a chosen
representative, quotient exactness turns those equalities into the
isomorphisms required by the class-effectivity construction. Its normalization
produces a global rigidified class restricting to the given local class.
Faithfully flat separation from the explicit isomorphism-descent hypothesis
gives uniqueness of this amalgamation.

`classPresheaf_isSheafFor_affineFlat` is the general slice statement.
`classPresheaf_isSheafFor_affine` specializes it to the slice morphism induced
by a flat surjective map `Spec R' → Spec R`, for arbitrary commutative rings
in universe `u` and an arbitrary structure map `Spec R → S`. This is the
affine singleton hypothesis of the separate fppf site criterion.

The result is derived from the Library's actual class presheaf, conditional
carrier descent and normalization, and conditional faithfully flat separation.
It does not prove either ordinary descent proposition, discharge uniqueness,
or by itself prove the full rigidified fppf comparison.
