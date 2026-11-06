# Coefficient automorphisms on the extended original integral image

For the same commuting coefficient square as `IntegralPointDescent`, let
`σ : L ≃ₐ[K] L` preserve and reflect membership in the actual range of `A → L`.
The supplied model `M`, its generic identification, its actual coefficient
base change, and the existing `rationalConjugate K L G σ` are retained.

`mem_baseChange_coefficientIntegralPoints_conjugate_iff` applies the original
generic-coordinate criterion. Coefficient conjugation replaces each regular
function value by its image under `σ`. The stated ring-preservation hypothesis
therefore gives preservation and reflection of integrality.

`mem_baseChange_integralPoints_rationalConjugate_iff` transfers this result
through the existing multiplicative comparison with rational points of the
actual base change. `baseChangeIntegralPointAut` restricts that same existing
rational conjugation to an actual multiplicative automorphism of the integral
subgroup. Its inverse is the inverse of the existing ambient automorphism.

This is an internal derivation from the published coordinate criterion and
coefficient-evaluation naturality. It assumes no finite-degree or Galois
extension condition, topology, reductivity, smoothness, or building data.
Ring preservation is an explicit hypothesis. This result constructs no
canonical model, special point, building descent map, or building comparison.
