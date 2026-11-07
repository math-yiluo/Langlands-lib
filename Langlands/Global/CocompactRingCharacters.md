# Character parametrization from a cocompact field in a ring

This internal supporting module connects the compact quotient character theorem to
the multiplication pairing of a commutative topological ring. The field and ring
may lie in different arbitrary universes. It does not prove the arithmetic
self-annihilator or restriction matching assertions.

`fieldImage` is the additive image of the field embedding, with the additive group
of the ring written multiplicatively. `fieldCharacters` is the subgroup of
continuous characters with parameters in that image. The quotient has its usual
quotient topology and is explicitly required to be compact and Hausdorff.

For `exists_field_parameter`, the base character is trivial on the field, and the
annihilator of the field is assumed to equal the field image. Field parameters
therefore give characters trivial on the image. Conversely, the annihilator
identity shows that these characters detect every point outside the image,
using commutativity of the ring. The compact quotient completeness theorem then
puts every continuous character trivial on the image in this subgroup. Unpacking
the range gives the required field parameter, with evaluation exactly
`psi(iota(k) * x)`.

For `pairing_surjective`, restriction matching is a further explicit premise.
Given any continuous character, choose a ring parameter with the same restriction
to the field and divide out its multiplication character. The quotient character
is trivial on the field, so the preceding result supplies a field parameter.
Adding the two parameters recovers the original character on the full ring.

The proof route is the generic Claim 1 and final surjectivity step of Worker
1843's adelic plan, using the independently submitted compact-character and
quotient-character helpers. This is a direct internal derivation; it asserts
no additional literature correspondence and does not establish actual adelic
self-duality until its stated arithmetic premises are proved.
