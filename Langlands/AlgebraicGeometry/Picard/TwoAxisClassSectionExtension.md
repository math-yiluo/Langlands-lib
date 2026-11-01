# Two-axis class extension from an explicit representation

This internal consumer takes a representation of the published compatible
two-axis-rigidified line-bundle class presheaf as an explicit input. It does
not construct a representer or prove its existence.

For schemes `S`, `X` and `T` in arbitrary universe `u`, an abelian scheme `A`
over `S`, a morphism `p : X ⟶ S`, and
`r : (classPresheaf A).RepresentableBy (Over.mk p)`, `sectionClassEquiv A p r b`
identifies actual maps `s : T ⟶ X` satisfying `s ≫ p = b` with `Classes A
(Over.mk b)`. The first equivalence identifies the subtype with morphisms in
`Over S`, using `Over.homMk` and `Over.w`; the second is the supplied
`r.homEquiv`. Thus both rigidifications and their compatibility are retained
in the representatives defining the classes.

`sectionClassEquiv_toBase` identifies restriction of an actual section along
the exact map `b` with `classesPullback A (TwoAxisFamily.toBase b)`. Its proof
is the naturality law `r.homEquiv_comp`. In particular the result does not
replace the chosen fraction-field map by a different generic-point map.

For a normal noetherian domain `R`, any chosen fraction field `K`, and an
explicit representation by `q : Y ⟶ Spec R`, assume that `q` is separated,
locally of finite type, formally unramified and satisfies
`DiscreteValuativeCriterion.Existence q`.
`classesPullback_surjective_of_normal_discreteValuativeExistence` proves
surjectivity of class restriction along the specified `R`-algebra map to `K`.
The proof sends a prescribed class through the inverse equivalence, extends
the resulting actual map with the published normal-noetherian section
theorem, and applies the restriction compatibility.

`actualBundleExtension_of_normal_discreteValuativeExistence` then consumes
this surjectivity in the published
`actualBundleExtension_of_classesPullback_surjective`. Its remaining inputs
are an actual line bundle on the generic self-product of the actual base
change of `B`, and the two nonempty actual axis-triviality isomorphism types.
It produces an actual line bundle `E` on the total self-product and a
nonempty actual module-sheaf isomorphism from its pullback along precisely
`mumfordProductBaseChangeMap B (Spec.map (CommRingCat.ofHom (algebraMap R K)))`
to `D`. The imported reduction constructs compatible rigidifications,
extracts a representative from the preimage class, and transports through
the identity base-change comparison. No extension of the chosen axis
trivializations is asserted.

Finally,
`Langlands.AbelianScheme.valuationRingTwoAxisExtension_of_normalFiniteTypeExtension`
supplies the published unconditional `normalFiniteTypeSubalgebra` theorem
to the published normal-model reduction. Its sole outer premise is still
`NormalFiniteTypeTwoAxisExtensionProperty.{u}`: actual extension for normal
finite-type integer domains and their canonical fraction fields. This
corollary removes the already proved normal-stage existence premise, while
retaining the unproved extension premise. It does not use the explicitly
represented normal-noetherian result to manufacture representation data.

This is internal composition of published Library constructions and Mathlib
`Functor.RepresentableBy`. No new literature assertion, unconditional
representability or unconditional valuative existence theorem is supplied.
The first extension theorem retains all the representation, geometric,
noetherian and discrete valuative existence hypotheses stated above. The
last corollary retains its finite-normal extension premise. The
arbitrary-valuation two-axis extension statement remains unproved.
