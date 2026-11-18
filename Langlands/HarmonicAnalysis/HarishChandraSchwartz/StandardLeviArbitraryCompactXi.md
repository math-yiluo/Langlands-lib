# Coefficients on the actual standard Levi with an arbitrary source compact

This derived internal module extends the canonical-Levi spherical transport
to an arbitrary displayed compact open subgroup of the literal standard Levi,
and proves its global coefficient bound from the original central-subgroup
square-integrability data. It combines published rational Levi identifications
with the central square-integrability transfer and full basis/Cartan inheritance.
No new original-literature statement is asserted.

Let `G` be connected reductive over an arbitrary nonarchimedean local field,
with maximal split torus `i`, generic cocharacter `ν` and a standard face `J`.
Write `M` for its literal rational-point standard Levi and `L` for its canonical
Levi scheme. Let `KM` be any compact open subgroup of `M` with the displayed
factorization `M = (P₀ ∩ M) KM`.

`leviSchemeSourceCompact` is the exact preimage of `KM` under
`leviSchemePointsEquiv`. Its openness and compactness follow from this point
homeomorphism. `isIwasawaPair_leviSchemeSourceCompact` transports the displayed
factorization using the exact preimage description of the intrinsic minimal
standard parabolic. No ambient compact whose intersection equals `KM` is
assumed.

`standardLeviMinimalModulusOf_eq_one_sourceCompact` proves that the actual
minimal Levi modulus is trivial on its intersection with `KM`. It lifts the
point to `L`, applies the intrinsic compact-open modulus theorem, and uses
`standardLeviMinimalModulus_leviHom`. `rationalXi_leviSchemeSourceCompact` then
identifies the intrinsic spherical function with the literal source spherical
function, using the actual subgroup and character comparisons and normalized
Haar transport under the point homeomorphism.

`hasXiBoundedCoefficients_standardLeviArbitraryCompact` takes the original
irreducible admissible representation of `M`, its original central subgroup
`C`, its original Borel-compatible quotient measurable space and Haar measure,
and square integrability modulo that same `C`. Its remaining structural inputs
are the original ambient simultaneous standard basis at a compact subgroup
`K0`, and the standard-Levi Cartan cover at that same `K0`.

The proof reads the representation on `L` by canonical same-carrier pullback,
takes the literal preimage of `C`, and transports the original quotient Haar
measure through the actual quotient homeomorphism. Square integrability is
preserved with that measure. A split component of `L` is supplied by the
published standard-Levi split-component theorem. Full intrinsic basis and
Cartan data follow from `SimultaneousStandardBasisAt.leviScheme` and
`finiteCartanCovering_leviScheme`, at the exact inherited original `K0`.
The arbitrary-central-subgroup global coefficient theorem on `L` applies,
and the new exact spherical comparison and smooth-dual pullback comparison
return the bound for the original literal representation and coefficients.

Thus each original coefficient is bounded everywhere on `M` by a positive
constant times its displayed `KM` spherical function. There is no added
valuation-index, matrix-height, explicit split-component or intrinsic
basis/Cartan hypothesis. The field and representation universes remain
independent. The source compact factorization remains a premise to this
module's bound; a projected compact specialization can derive it from the
original ambient factorization. No ambient simultaneous-basis existence or
wave-packet Schwartz conclusion is claimed.
