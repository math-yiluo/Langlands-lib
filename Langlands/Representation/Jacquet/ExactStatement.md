# Compact detection and exactness of smooth coinvariants

`Langlands.SmoothCoinvariantExactnessStatement` combines the compact detection
of coinvariant relations with exactness of the corresponding quotient maps.
It is a proposition definition, with no assumed truth or proof of either claim.

The group is a topological group with the explicit hypothesis

> Every finite subset is contained in a compact open subgroup.

The coefficient field is the complex numbers. The group and three module
carriers have independent universes. The modules have no topology and need
not be finite dimensional, finitely generated, admissible, or irreducible.

The first clause says that a vector in the span of the relations
`rho(g)v - v` already belongs to the relation span for one compact open
subgroup. The converse inclusion is included in the equivalence. This clause
is quantified over smooth representations, matching the subsequent exactness
setting, although its finite-span argument does not itself require smoothness.

The second clause starts with actual equivariant linear maps
`i : U → V` and `p : V → W`, explicit injectivity and surjectivity, and
`range i = ker p`. It assumes that the middle representation is smooth.
It asserts injectivity, equality of image and kernel, and surjectivity for
Mathlib's induced maps on coinvariants. The two end representations inherit
smoothness from these hypotheses; it is not an additional premise.

`Representation.Coinvariants.ker rho` is Mathlib's submodule spanned by
the actual relations, despite the word `ker` in its name. The coinvariant
carrier is the actual module quotient by this submodule. Both induced maps
are `Representation.Coinvariants.map`; the statement does not substitute
arbitrary quotient objects or maps.

## Original source and derived scope

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III, *Induced representations and the Jacquet module*, April 29, 2019:
Lemma III.3.1 and the quotient definition on page 3; Lemma III.3.3(a)-(b)
and Proposition III.3.4 with its proof on page 4. The chapter's ambient
reductive-group conventions and normalized induction on page 1 were also
read. The entire eight-page chapter was read in the retained original.

- Literature ID: `casselman-2019-jacquet-module`.
- Original PDF SHA256:
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
- Original file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.

Casselman proves the compact-open exhaustion property for p-adic unipotent
groups in III.3.1, then uses it to detect relations in III.3.3 and prove
exactness in III.3.4. This target is a derived formulation that isolates the
finite-subset containment hypothesis actually used by that argument, and
specializes the coefficient ring to the complex numbers. It makes no claim
that an arbitrary reductive group has that containment property.

Concretely, a vector in the relation span is a finite sum involving finitely
many group elements. The hypothesis puts those elements in a single compact
open subgroup, giving the first clause. Surjectivity and middle exactness
of the induced quotient maps are algebraic. For injectivity, a relation in
the middle representation is detected in such a compact subgroup; normalized
finite averaging then detects it in the subrepresentation as well. Over
complex coefficients all finite indices used in this averaging are invertible.
This does not assert exactness over arbitrary coefficient rings.

Casselman's III.3.3(c), the averaging-zero characterization, is not restated
using an integral on an unspecified module topology. Its finite-averaging
ingredient belongs to the existing compact-averaging infrastructure. No
new averaging construction or unipotent-group geometry is defined here.
The later proof can reuse those exact accepted results.

For a parabolic Jacquet functor the group in this target is the unipotent
radical, after restricting the ambient representation. The action of the
Levi subgroup and the inverse-half-modulus twist do not change the underlying
sequence of linear maps. Their actual constructions and the geometric
verification of the compact-open containment hypothesis remain separate
interfaces; this file does not claim their construction or their specialization.

## Mathlib audit and exact dependencies

At Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
`RepresentationTheory/Coinvariants.lean` defines the relation span, quotient,
quotient map, induced map, and map identity/composition laws. It also provides
the algebraic adjunction to trivial representations. This file reuses those
objects directly. It does not duplicate the normalizer-action construction
owned by Worker 34. That construction's `Jacquet.Coinvariants` and
`Jacquet.relations` abbreviate the same Mathlib objects after restriction.
No unreviewed Jacquet draft is imported.

The only project import is `Langlands.Representation.Smooth.Definitions`,
artifact `665022df-625b-44ae-9dbd-425f6e266bab`, version 1. Its accepted
Lean and Markdown hashes are respectively
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` and
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.
Its publication commit is `10c81beaaff024987cf2945c64d0c9511f6cb686`.
A fresh fetch verified that it remains accepted, published and current at
Library head `9007729971e6e6ecea63b5567b6d1621769ccfb0`, with no missing,
changed or unavailable dependencies; both local source hashes match.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 and the pinned Mathlib commit above.
Worker 8 authored this pair. Independent statement review, publication and
a later theorem proof are distinct obligations.

Development check `354eba7e-c307-4af7-8377-8236a9b870cd` compiled the pair
with zero warnings or errors using the shared incremental Lake build.
Exact declaration inspection returned `statement_returns_prop: true` and
target fingerprint
`b03b5757470275264b27d3099b503d4d2f41aab376526d75b62cdf66c40e7664`.
A separate `#print` inspection confirmed the four independent universes,
the internal topological-group and finite-subset containment hypotheses,
the smooth-middle premise, and the actual three conclusions about the
induced maps. These are development findings, not semantic or proof acceptance.
