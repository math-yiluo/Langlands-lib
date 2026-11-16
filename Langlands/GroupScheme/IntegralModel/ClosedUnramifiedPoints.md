# Integral coordinates through a closed model over the unramified extension

This is an internal derived helper for the doubled-root depth-model construction.
It combines the Library's closed-subgroup integral-point criterion, coefficient
base change of a model homomorphism, and the comparison between integral model
coordinates and integral points over the maximal unramified extension. It makes
no independent claim about constructing an integral model or a building.

Fix an arbitrary universe `u`, a nonarchimedean local field `F`, actual group
schemes `U` and `G` over `F`, integral models `M` of `U` and `N` of `G` over
`𝒪[F]`, a generic homomorphism `q : U ⟶ G`, and a compatible model
homomorphism `φ : M.Hom N q`. Assume that `φ.hom` is a closed subgroup
inclusion. Neither smoothness nor connectedness is needed.

`IntegralModel.hasIntegralCoordinates_iff_map_mem_baseChangeUnramified`
proves the following equivalence for **every** point
`x : rationalPoints (baseChanged F (UnramifiedClosure F) U)`: the original model
`M` has integral coordinates at `baseChangeCoeffEquiv F (UnramifiedClosure F) U x`
if and only if the image of `x` under the actual base change of `q` belongs to
`N.baseChangeUnramified.integralPoints`. No hypothesis restricts `x` to the
extension of an `F`-point.

The proof first uses
`IntegralModel.mem_baseChangeUnramified_integralPoints_iff` to identify the
left side with membership in `M.baseChangeUnramified.integralPoints`.
The coefficient comparison and its inverse cancel at `x`.
`Hom.baseChangeCoefficients` extends `φ` to the actual integer ring
`fixedFieldIntegers F` in `inertiaFixedField F`, and
`Hom.isClosedImmersion_baseChangeCoefficients` preserves its closed inclusion.
The Library theorem `Hom.integralPoints_eq_comap` then identifies the integral
points of the changed model with the preimage of the ambient integral points
under the actual changed generic map. This equality gives both directions of
the claimed equivalence. The fraction-field and integer-ring scalar tower are
the standard ones from `Valuation.HasExtension`.

All mathematical inputs are already proved in the imported Library modules
`IntegralModel.BaseChangeCoefficientHom`, `IntegralModel.SchematicClosure`,
and `LocalUnramifiedTwistDescent`; this helper introduces no new source claim.
In particular, the unproved model-existence proposition in `SchematicClosure`
is not used.
