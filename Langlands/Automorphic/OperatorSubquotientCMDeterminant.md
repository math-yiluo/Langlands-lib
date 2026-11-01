# CM conjugation and determinant transport of actual operator quotients

This internal derived construction works over a CM number field `K` in an
arbitrary universe `uK`, for every natural matrix rank `n`, with complex
coefficients. The character `χ` is an actual Hecke character of finite order;
the proof of finite order is an explicit argument. Its arithmetic CM pullback
is `χC = χ.complexConj`, whose finite order follows from
`HeckeCharacter.hasFiniteOrder_complexConj_iff`. Complex values are fixed.

## Arithmetic and concrete operator compatibility

`HeckeCharacter.adelicDeterminant_complexConj` proves

`χC.adelicDeterminant n g = χ.adelicDeterminant n (CMConjugation.adelicConj K n g)`.

The proof unfolds actual character pullback on idele representatives and uses
`AdelicGLTransport.determinant_adelicEquiv`, specialized to the genuine CM
field automorphism. This is an identity of actual complex units.

Write `J` for the published finite-smooth CM argument pullback and `Mχ` for
the actual finite-order determinant multiplier. The theorem
`FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_complexConj`
proves `J (Mχ f) = MχC (J f)` on the actual finite-smooth function carrier.
Three subtype extensionality steps reduce this to function evaluation, where
the arithmetic character identity gives the result.

`determinantOperatorConjugation_cmOperatorConjugation` proves, for every
operator `a` of the concrete automorphic operator algebra,

`Cχ (Ccm a) = Ccm (CχC a)`.

Here `Cχ` and `Ccm` are the actual published algebra automorphisms, defined by
conjugating ambient operators with the respective actual linear equivalences.
The proof applies extensionality, then injectivity of `Mχ` and `J`. The two
published whole-operator covariance identities and the multiplier identity
identify the resulting function values. The identity covers the entire
concrete operator algebra, not only its specified generators.

## Actual mixed quotient comparison

For an actual `Q : OperatorSubquotient K n`, let

- `X = (Q.determinantTwist χ hχ).complexConj`;
- `Y = Q.complexConj.determinantTwist χC hχC`.

Both have actual module-quotient carriers with the inherited whole concrete
operator action. Write `Dχ` and `JQ` for the published induced quotient linear
equivalences, with the carrier indicated by their subscripts below. The two
actual complex-linear equivalences from `Q.Space` are

`eX = J_(Qχ) ∘ Dχ` and `eY = DχC_(Qcm) ∘ JQ`.

`Q.determinantTwistComplexConjEquiv χ hχ` is a genuine
`X.Equivalence Y` with underlying linear equivalence `eY ∘ eX⁻¹`.
The imported `composedConjugationQuotientCovariance` composes covariance.
The concrete mixed operator identity makes the two resulting parameter maps
identical. The imported `sameConjugationQuotientEquiv` then proves that
`eY ∘ eX⁻¹` intertwines the unchanged whole operator
actions, using surjectivity and inverse cancellation. No input intertwiner or
identification of dependent quotient presentations is assumed.

`determinantTwistComplexConjEquiv_apply` identifies the map on every vector
`x : X.Space` with

`DχC_(Qcm) (JQ (Dχ⁻¹ (J_(Qχ)⁻¹ x)))`.

`determinantTwistComplexConjEquiv_apply_equiv` proves the exact source-vector
formula `E_Q (eX v) = eY v` for every `v : Q.Space`, by cancellation of the
two actual inverses. These are formulas on quotient vectors, with no evaluation
of quotient vectors as functions.

## Naturality and classes

`Intertwiner.determinantTwist_complexConj_naturality` proves

`LY ∘ E_Q = E_T ∘ LX`

for every supplied whole-action intertwiner `L : Q.Intertwiner T`. Here `LX`
is determinant transport followed by CM transport of `L`, and `LY` is CM
transport followed by determinant transport by `χC`. Surjectivity of `eX`
reduces the calculation to an original quotient vector. Explicit congruence
and transitivity combine the comparison formula with the published exact
application formulas for both transported maps.
`Equivalence.determinantTwist_complexConj_naturality` proves the corresponding
equality of genuine representation equivalences by applying the intertwiner
identity pointwise to the supplied equivalence's underlying map.

Quotient induction and the constructed whole-action equivalence prove
`IsoClass.complexConj_determinantTwist`:

`complexConj (determinantTwist c χ hχ) = determinantTwist (complexConj c) χC hχC`.

## Provenance and boundaries

These constructions are derived from the published arithmetic character
transport, actual finite-smooth multipliers, CM and determinant operator
conjugations, and actual operator subquotients and their map/class transports.
The covariance helpers are reused directly from
`OperatorSubquotientDeterminantAction`; no new
identification with original literature is made. The module imports only
published prerequisites and does not depend on
`OperatorSubquotientDeterminantNaturality`.

The result is algebraic. It asserts neither quotient topology nor evaluation,
nonzero or irreducible occurrence, spectral existence, selected local factors,
nor general coherence identities. The CM hypothesis is essential to the
operations used here. No positivity assumption on rank or extra preservation
hypothesis on the actual quotient is introduced.
