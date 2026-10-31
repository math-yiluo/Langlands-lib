# Intrinsic Whittaker models of generic representations

Author: Worker 31.

This module constructs the intrinsic Whittaker function model from the
published all-functional set `RankinSelberg.whittakerSet`. For a generic
representation over a specified p-adic field, its hypotheses are exactly the
existing `Whittaker.IsGeneric`: irreducibility, admissibility (including
smoothness), and existence of a nonzero standard Whittaker functional.
Scalar uniqueness is supplied by the published `Whittaker.multiplicityOne`
theorem. It is not an extra input to the generic construction.

The field universe `uF` and representation-carrier universe `uV` are independent.
Coefficients are complex numbers. Positive rank is `n + 1`, including rank one.
The p-adic section uses `PadicField.canonicalNormedField`, and hence the canonical
field and matrix-group topology. No topology on the representation carrier or
its algebraic dual is installed or required. The shared
`HarmonicAnalysis.UnitaryAdditiveCharacter`, actual matrix upper-unipotent
subgroup, and standard character are reused without alteration.

`isOfWhittakerType_of_isGeneric` extracts a nonzero functional from genericity.
The published multiplicity theorem proves that every functional is a scalar
multiple of it. The published algebraic
`whittakerTypeFromMultiplicity` then gives all three clauses of the existing
JPSS `IsOfWhittakerType`: admissibility, finite generation over the complex
group algebra, and a linear equivalence from the full functional space to
`ℂ`. In that algebraic proof, irreducibility makes the group-algebra module
simple and therefore finitely generated; the scalar map from `ℂ` is bijective
by nonvanishing and the spanning property.
`isOfInverseWhittakerType_of_isGeneric` uses the published diagonal character
change at `-1` to obtain full inverse-character type for the same
representation, as needed for the second member of a JPSS pair.

The general construction `whittakerModel` takes full standard Whittaker type
on a representation over a topological field. It is a subrepresentation of
the existing space of standard character-equivariant functions. Its submodule
carrier is definitionally `whittakerSet ψ n π`: a function belongs precisely
when it is `g ↦ ℓ (π g v)` for some Whittaker functional `ℓ` and vector `v`.
No preferred functional is an argument or a choice in the carrier. To prove
closure under addition and scalars, the proof uses the published scalar-span
lemma to identify this set with the image for any nonzero functional. Right
translation preserves each coefficient image. The theorem
`whittakerModel_eq_coefficientModel` proves equality of subrepresentations with
the image for every nonzero functional, rather than only an abstract
isomorphism between the spaces.

`whittakerModelRepresentation` restricts the existing right-translation action
to this submodule. `whittakerModelFunction` exposes the actual complex-valued
function. Its proved formulas are

- `W(u * g) = standardCharacter ψ n u * W(g)` for an actual upper-unipotent `u`;
- `(π_model(s) W)(g) = W(g * s)`.

`whittakerModelMap` is the actual coefficient intertwiner
`v ↦ (g ↦ ℓ (π g v))`, with codomain restricted to the intrinsic model.
For nonzero `ℓ`, it is surjective: equality of the intrinsic model with the
coefficient image supplies a preimage. For an irreducible original
representation, `whittakerModelEquiv` upgrades this map to a representation
equivalence. Its injectivity is inherited from the published equivalence to
the specified coefficient image; the two maps have the same underlying
functions. The chosen `ℓ` fixes the normalization of this equivalence, while
the target model itself remains independent of that choice.

`whittakerModel_isSmooth` uses a coefficient preimage of each model vector:
an open subgroup fixing the preimage also fixes its image by intertwining.
This proof includes reducible representations of full Whittaker type.
When the original representation is irreducible,
`whittakerModel_isOfWhittakerType` transports all three clauses along the
constructed equivalence. No assertion that the model of every reducible
representation is equivalent to that representation is made.
Every intrinsic model function is locally constant, and consequently
continuous, when the field is a topological ring. The proof applies the
published matrix-coefficient local-constancy theorem to the actual functional
and vector witnessing membership in the intrinsic set, using the original
admissibility's smoothness clause.

`genericModel` and `genericModelRepresentation` specialize these actual
constructions using the proved generic-to-full-type bridge. Membership is
still exactly membership in the existing intrinsic set.
`genericModelEquiv` realizes the original generic representation in this
model for any supplied nonzero functional, and its evaluation formula is
proved to be exactly `ℓ (π g v)`.
`genericModel_isOfWhittakerType` records all three inherited clauses.

This is a derived construction from the published
[all-functional set](LocalFactor.md),
[algebraic coefficient models](../Whittaker/Algebraic.md),
[actual general-linear specialization](../Whittaker/GeneralLinear.md),
[multiplicity theorem](../Whittaker/MultiplicityOneProof.md),
[full-type algebraic bridge](WhittakerTypeFromMultiplicityProof.md),
[model and character adapters](WhittakerGammaAdapters.md), and
[equivalence transport](WhittakerTypeEquivalence.md).
It assembles these existing abstractions and proves the submodule, action,
surjectivity and equivalence obligations; it introduces no new representation
hierarchy or mathematical axiom.

The original mathematical construction is JPSS, *Rankin–Selberg Convolutions*,
American Journal of Mathematics 105 (1983), Section 2.1, printed pp.385–386.
Page 385 gives the covariance relation, full Whittaker-type conditions,
zero-or-one multiplicity for irreducibles, genericity and character inversion.
Page 386, equation (3) and its following paragraphs, defines the all-functional
space, its right action, its quotient realization, and its equivalence with
the original representation when irreducible. The retained original scan's
PDF pages 20–21 were read visually for this contribution. Registered source:
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
No source-specific errata note was present in the project or current Library
`notes/errata` locations checked. The implementation route uses the already
proved multiplicity theorem and algebraic adapters; its mathematical model
and normalization agree with those original passages.

This construction does not prove genericity of arbitrary irreducible
representations, analytic continuation, functional equations, normalized
polynomial existence, or classification. Those remain their separate
explicit prerequisites. It constructs the intrinsic model and its proved
representation structure, rather than selecting an L, epsilon or gamma value.
