# Actual unramified normalized induced family

The first section is generic. For a commutative complex algebra `B`, a
`B`-linear group representation on a module that is also a complex module
through a scalar tower, a complex representation, a ring homomorphism
`e : B →+* ℂ` restricting to the identity on complex scalars, and an
`e`-semilinear map `T` commuting with the two group actions,
`restrictedIntertwining` is `T` regarded as a complex intertwiner out of the
published complex restriction `Jacquet.CoefficientRestriction.complexRepresentation`.
`restrictedIntertwining_smul` records the scalar law
`f (b • x) = algebraMap B ℂ b • f x` for the algebra structure `e.toAlgebra`,
and `restrictedIntertwining_bijective` states that bijectivity of the published
`Plancherel.scalarExtensionOfSemilinear T` gives bijectivity of the published
`Compact.CoefficientSpecialization.scalarExtension` of this intertwiner; the two
maps agree by definition.

The remaining sections apply the published universal normalized induction to
the literal Levi image of an actual rational parabolic. Its coefficient
algebra consists of the regular functions on the transported full unramified
parameter group. The inducing representation is the original representation
pulled back along the inverse Levi-point equivalence.

`universalFamily` restricts this native coefficient-linear action to complex
scalars on the same full smooth induced carrier. `fiber` is exactly the
published `leviInductionFunctor` applied to the original representation twisted
by the original unramified character.

The coefficient module, its scalar tower over the complex numbers, and the
compatibility of coefficients with every group operator are recorded as
explicit instances on the bundled carrier of `universalFamily`.
`universalFamily_fixed_finite_free` states that, for an admissible inducing
representation and a compact parabolic quotient, the fixed vectors of every
compact open subgroup form a finite free coefficient module. The proof pulls
admissibility back to the Levi image, applies the published finite-free theorem
for rational normalized induction, and transports the result along the identity
equivalence of fixed-vector carriers.

`specializationEvaluation` is the published `UnramifiedNormalized.inducedEvaluation`
at the transported parameter `parameterEquiv ψ`, regarded through
`restrictedIntertwining` as a complex intertwiner from `universalFamily` to the
literal `fiber` at `ψ`; `specializationEvaluation_apply` records this by
definition. `specializationEvaluation_smul` is its scalar law along evaluation of
regular coefficients at `parameterEquiv ψ`. `universalFamily_specialization`
states, for a compact parabolic quotient and with the complex numbers made an
algebra over the coefficient algebra through the evaluation homomorphism from the
coefficient algebra to the complex numbers, that some intertwiner from
`universalFamily` to `fiber` with this scalar law has bijective coefficient scalar
extension, that is, the induced map from the tensor product of the complex
numbers with `universalFamily` over the coefficient algebra to `fiber` is
bijective. Its proof uses `specializationEvaluation` and the published generic
bijectivity `UnramifiedNormalized.Specialization.inducedScalarExtension_bijective`
from the supporting generic specialization module,
with closedness of the parabolic image, continuity of the norm family and
continuity of the Levi projection. This comparison needs no admissibility.

The field and representation carrier have independent universes. The
canonical point topology is used, the ambient rational-point group is locally
compact and nonarchimedean, and the actual parabolic, rational Levi, geometric
unipotent radical, and isomorphic multiplication morphism remain explicit.
Affineness of the ambient group and Levi is explicit and is available from
their connected reductivity in the host statement.

This module is internal derived content. It uses the supporting actual Levi
parameter transport (`normFamily`, `parameterEquiv`) and generic normalized
induced specialization modules, which are included with it, together with the
published Levi-point transport, coefficient scalar restriction, universal
normalized induction, finite-free and evaluation APIs, following the base-change step of Renard VI.8.2
(PDF pp.196–197) used in VI.8.4 (PDF pp.198–199). It does not prove induced
irreducibility or supply admissibility, quotient compactness, or a detecting
compact subgroup.
