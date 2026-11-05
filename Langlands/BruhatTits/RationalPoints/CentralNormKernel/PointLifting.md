# Rational points of a closed subgroup of `GL_n` through the coordinate ring

Author: Worker 1532.

Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`. Internal helper for the
proof of `CentralNormKernelCompactnessStatement`. Let `K` be a field, `G` a group scheme over
`Spec K` and `ρ : MatrixRepresentation G n`.

- `coordMap ρ : GeneralLinear.CoordinateRing n K →+* Γ(G.X.left, ⊤)` is pullback of the
  coordinate functions of `GL_n` along `ρ` (after `Scheme.ΓSpecIso`). `coordMap_algebraMap`: it
  sends scalars to `scalarMap G.X`.
- `classify_rationalMatrix`: for a rational point `x`, the classifying map
  `GeneralLinear.classify (ρ.rationalMatrix x)` equals `evalPoint x ∘ coordMap ρ`, where
  `evalPoint` (from `GroupScheme.Derived.CentralIntersection.Unipotence`) evaluates global
  functions at `x`. Both are ring maps out of a quotient of a polynomial ring, so it suffices to
  compare them on constants and on the entry and inverse-entry variables
  (`GeneralLinear.classify_entry`, `classify_inverseEntry`,
  `MatrixRepresentation.rationalMatrix_apply_apply`, `GeneralLinear.pointsEquiv_inv_apply`).
  `classify_rationalMatrix_apply` is the pointwise form, and `classify_rationalMatrix_eq_zero`
  says matrices of rational points kill `RingHom.ker (coordMap ρ)`.
- `affineCoordinateMap_eq_scalarMap`: the structure map of the published affine coordinate ring
  is `scalarMap`. This is the same argument as the `Type`-universe lemma
  `PointManifold.affineCoordinateMap_eq_appTop`, stated in every universe.
- `exists_rationalMatrix_eq` (**lifting**): if `G.X.left` is affine and `ρ` is a closed
  immersion, every `g : GL n K` whose classifying map kills `RingHom.ker (coordMap ρ)` is
  `ρ.rationalMatrix x` for some rational point `x`. Proof: `coordMap ρ` is surjective
  (`IsClosedImmersion.isAffine_surjective_of_isAffine`), so `classify g` factors through it as a
  ring map `ψ₀ : Γ(G.X.left, ⊤) →+* K` (`RingHom.liftOfSurjective`), which is a `K`-algebra map
  for the published algebra structure. The published equivalences `affineSchemePointEquiv` and
  `rationalPointEquiv` turn `ψ₀` into a rational point `p`, and
  `affineSchemePointEquiv_apply_eq_evaluation` shows `evalPoint p = ψ₀`. Then
  `classify (ρ.rationalMatrix p) = ψ₀ ∘ coordMap ρ = classify g`, so the matrices agree
  (`GeneralLinear.homEquiv`).
