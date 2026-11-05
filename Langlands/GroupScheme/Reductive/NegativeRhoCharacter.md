# Negative-rho character from a dynamic Levi retraction

This is an internal construction from supplied actual group schemes and dynamic
subgroup representatives. For an ambient separated group scheme and a
cocharacter, suppose `H` represents its dynamic parabolic and a supplied
commutative group `T` represents its dynamic centralizer. The additive map
`extendCentralizerCharacter` extends each character of `T` to `H` by composing
with the published actual morphism `Dynamic.limitGroupHom`. Its restriction
along `centralizerToParabolic` is the original character, because that inclusion
is a section of the limit map. Thus the extension is injective, and the module
also proves its evaluation formula on every relative test scheme.

Over a field, a supplied integral root datum on the actual character and
cocharacter lattices of `T`, a base, and full integral coroot span construct
`negativeRhoCharacter` on `H`. Its restriction is exactly the negative integral
Weyl vector. If the supplied datum is a root datum of the actual map `j`, the
restricted character pairs with every coroot as the negative height in the
dual base; those integers are nonzero.

When `H` is affine, `negativeRhoCoordinate` is the actual affine coordinate of
this character. Its values, including its restriction to the centralizer,
are proved on arbitrary relative test schemes. Each value is a unit. The
proofs use the published character-coordinate evaluation identity and the
same section/retraction law, without restricting tests to rational points.

No Borel, torus, root datum, or full coroot span is asserted to exist here.
The construction applies to a dynamic Borel once those data are supplied; it
does not prove highest-weight representation existence, a matrix-coefficient
support statement, or Steinberg irreducibility. Its provenance is the internal
composition of the dynamic Levi retraction with the integral Weyl-vector
construction, not an imported representation-theoretic theorem.
