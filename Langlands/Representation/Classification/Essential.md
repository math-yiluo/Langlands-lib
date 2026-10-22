# Explicit real exponents and essential analytic properties

Worker 23 defines actual exponent witnesses, using the genuine positive character
`nu : G -> NNReal units` and the constructed action `realPowerTwist`.
`UnitaryExponentData nu rho` consists of a real exponent `s` and an invariant
positive definite form for `nu^(-s) rho`. `SquareIntegrableExponentData nu rho mu`
consists of `s` and square-integrability modulo the center of `nu^(-s) rho`,
using the actual central quotient and the specified Borel Haar measure `mu`.
`IsEssentiallyUnitarizable` and `IsEssentiallySquareIntegrableModCenter` assert
nonemptiness of the corresponding witness types.

The normalized representation is constructed on the original algebraic module
by removing that exponent. The reconstruction equality `rho = nu^s rho_u`
follows from the proved cancellation of real-power twists. The `shift`
constructors send a witness of exponent `s` to one of exponent `s+t` for
`nu^t rho`; their fields use the proved equality of the normalized actions.
The square-integrable normalized action is admissible by definition. If `nu`
has open kernel, the original action is smooth by the accepted twist theorem.
No norm, topology, completeness, or finite dimension is required on the module.

The file also constructs transport through any actual equivariant linear
equivalence, including between different carrier universes. For a unitary
central character, the character homomorphism itself is unchanged and its
scalar-action field is transported by the equivalence. On the central
quotient, the transported coefficient norm equals the original norm with the
functional pulled back and the vector transported inversely. The accepted
`contragredientMap` supplies this pullback as an actual smooth functional.
Together with the accepted `isAdmissible_of_equiv`, this proves invariance of
square-integrability modulo the center. The `ofEquiv` constructors then
transport both kinds of exponent witnesses with the same exponent, yielding
invariance of both essential-property predicates. These intrinsic transport
proofs support later definitions on honest isomorphism classes.

These are derived generic constructions supporting Henniart 2002, section 2.8,
printed page 596 (PDF page 10), which writes an irreducible essentially
square-integrable GL representation as `nu^alpha pi_u`, with real `alpha`.
Its scalar-twist convention and normalized absolute value are on printed
page 595, section 2.5. The source ID is `henniart-2002-characterization`,
SHA-256 `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
The retained original pages 594--596 were read directly.
The square-integrability definition comes from the separately documented
Casselman 1995, section 2.5, page 28, implemented in `MatrixCoefficient/ModuloCenter`.
Its source ID is `casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.

The witnesses make no existence or uniqueness assertion. The two witness
types are independent: no theorem that square-integrability implies
unitarizability is assumed. The generic predicates do not impose
irreducibility; the GL classification classes must additionally impose it and
instantiate `nu` with the actual residue-normalized determinant norm.
They do not substitute an arbitrary classification predicate, unproved
Jacquet criterion or a canonical special/Langlands quotient.

The imported project constructions are
`Langlands.Representation.Twist.RealPower`,
`Langlands.Representation.MatrixCoefficient.ModuloCenter`,
`Langlands.Representation.Unitary.Basic`, and
`Langlands.Representation.Smooth.Admissibility.EquivalenceProof`.
They are published in Library commit
`1804f2a6d98d21c2bbfa3c73ccf807df74c484bb`; the complete imported project closure
of fourteen Lean/Markdown pairs matches that Library exactly.
The generic construction and transport proofs use Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Compilation checks the implementation; independent source correspondence
review and publication are separate requirements.
