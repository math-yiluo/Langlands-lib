# Fppf values of actual characters in supplied torus coordinates

This internal derived module connects the independent-monomial local lift to
actual characters on a torus with supplied coordinate isomorphism. Its general
API requires no reductive group or pinning. The affine base is the spectrum of
an arbitrary commutative ring, including the zero ring, and the test schemes
need not be affine.

For any scheme `S`, finite type `I`, torus `T`, and specified group-scheme
isomorphism `e : splitTorus S I ≅ T`, the homomorphism
`splitTorus.exponentCharacterOnTorus S T e m` is the composite of `e.inv` with
the actual fixed-exponent character `splitTorus.exponentCharacter S I m`.
The theorem `pointsEquiv_exponentCharacterOnTorus` evaluates this actual
character at the point obtained by transporting a coordinate point through
`e.hom`. Its value is the product of the point's global-unit coordinates
raised to the integer exponents `m`. The proof cancels the supplied
isomorphism and its inverse, then uses the published actual-character
monomial formula.

Let `R` be a commutative ring, let `I` and `J` be finite, and let the rows
`m : J → I → ℤ` be linearly independent over `ℤ`. Given a test scheme `V`
over `Spec R` and global units `c : J → Γ(V, O)ˣ`, the imported canonical
lift `L := splitTorus.exponentUnitsLift R m hm V c` has a flat, surjective,
locally finitely presented projection to `V`. The theorem
`exponentUnitsLift_character` states that its point, transported to `T`,
has character value `c j` pulled back along this projection, for every
row `j`. The proof combines the transported-character monomial formula
with the already established monomial equation.

`exponentUnitsLift_character_naturality` retains the same equation after
every morphism `b` to the covering test scheme. It follows from naturality
of the actual multiplicative-group point model and composition of
pullbacks on global units. Finally,
`exists_fppf_exponent_character_values` packages the covering test scheme,
its projection, the point of the supplied torus, all three geometric
properties, and the equations on every refinement.

The provenance is entirely internal: transport of the published actual
characters, the previously constructed pullback lift, and naturality of
their point models. Integral independence need not be saturated; no
smoothness of the projection is asserted. The separate simple-root
adapter applies this API to an `AffinePinnedModel`.
