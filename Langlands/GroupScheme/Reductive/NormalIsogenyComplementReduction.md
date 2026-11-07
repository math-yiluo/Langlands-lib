# Arbitrary-field normal complements from geometric generation and perfectness

`semisimpleNormalIsogenyComplementOfGenerationAndPerfectness` chooses an actual
commuting closed normal complement to a prescribed smooth connected closed
normal subgroup `H` of a semisimple group `G` over any field in universe `u`.
It records semisimplicity of `H`, of the chosen complement, and of their actual
product, and the central-isogeny property of their actual multiplication.
The construction takes two explicit structural premises:
`SemisimpleAlmostSimpleGenerationStatement` and
`AlgebraicallyClosedSemisimplePerfectStatement`, in the same universe.
No characteristic or perfectness condition is imposed on the original field.

The accompanying theorem
`semisimpleNormalIsogenyComplement_of_generation_and_perfectness` reduces the
exact existing `SemisimpleNormalIsogenyComplementStatement` to those same two
premises. Neither premise is proved here. Consequently this module does not
establish the unconditional host theorem.

The proof first chooses a closed representative `C` of the full centralizer of
`H` and a closed affine representative `D` of the full derived subgroup of `C`,
both over the original field. The composite `D → C → G` is closed, normal on
every test scheme, and commutes with `H` on every test. Unconditional
normal-subgroup semisimplicity proves that `H` is semisimple.

Base change to an algebraic closure preserves the full centralizer of the
original inclusion, including all test schemes and refinements. Normality also
base changes. The proof bundles this specific base-changed representative as a
full normal centralizer and takes its smooth connected reduced identity
component `K`. The explicit almost-simple generation premise makes the actual
multiplication `H` times `K` flat and scheme-surjective. Normality of this core
in the base-changed ambient smooth group gives its semisimplicity. The explicit
perfectness premise therefore makes `K` perfect. Affineness of the source and
target makes this multiplication quasi-compact, so it is fpqc.

The full-centralizer derived comparison then identifies `K` with the base
change of `D`, compatibly with its actual inclusion into the centralizer.
Semisimplicity reflects along the field extension, proving that `D` is
semisimple over the original field. Tensoring the comparison homomorphism with
the identity on the first factor gives a morphism whose composite with the
base-changed original multiplication is exactly the geometric core
multiplication. Scheme-surjectivity of this composite implies
scheme-surjectivity of the base-changed original multiplication, which reflects
to the original field. The finite full centres of the original semisimple
factors then give the central-isogeny property and semisimplicity of their
actual product source. This retains the full possibly nonreduced centres and
kernel, with no smoothness claim for either.

The data constructor chooses a witness from that reduction theorem and records
flatness and surjectivity supplied by its central-isogeny conclusion. All
normality and commutation assertions concern every relative test scheme.

The provenance is internal composition of the full-centralizer, reduced-core,
normal-subgroup semisimplicity, full-derived representability and comparison,
field-extension reflection, and finite-centre multiplication interfaces.
Authorship: Worker 1616. Worker 1783 supplied the geometric core and
multiplication-descent constructions used by this assembly.
