# Base change of central rational points and matrices to an algebraic closure

Author: Worker 1532.

Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`. Internal helper for the
proof of `CentralNormKernelCompactnessStatement`. Let `F` be a field and `M` a group scheme over
`Spec F`.

- `closureBase F` is `toAlgebraicClosure F`, and `closureGroup M` is the base change
  `(GroupScheme.baseChange (closureBase F)).obj M`, the group scheme appearing in
  `IsConnectedReductive.hasTrivialGeometricUnipotentRadical`.
- `closureRep ρ` is the base change of `ρ : MatrixRepresentation M N` followed by the published
  isomorphism `GeneralLinear.baseChangeIso`. `isClosedImmersion_closureRep`: it is a closed
  immersion when `ρ` is (`IsClosedSubgroup.baseChange`, composition with an isomorphism).
- `closurePoint z` is the rational point of `closureGroup M` corresponding, under
  `baseChangePointsEquiv`, to `z` restricted along `Spec K ⟶ Spec F`.
  `closurePoint_mem_center`: it is central when `z` is, by `center_baseChange`.
- `closureRep_rationalMatrix`: `(closureRep ρ).rationalMatrix (closurePoint z)` is
  `ρ.rationalMatrix z` with entries mapped to the algebraic closure. Proof: via
  `GeneralLinear.pointsEquiv_comp_baseChangeIso_hom`, `baseChangePointsEquiv_comp`,
  `GeneralLinear.pointsEquiv_naturality`, and `appTop_closureBase` (from
  `Scheme.ΓSpecIso_naturality`).
