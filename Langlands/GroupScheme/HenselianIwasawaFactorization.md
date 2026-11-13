# Integral-times-parabolic factorizations from strictly Henselian coverings

Module `Langlands.GroupScheme.HenselianIwasawaFactorization`, namespace
`Langlands.GroupScheme.HenselianParabolicCovering`. The published `HasLeftIntegralCovering`
results give the covering `H · M(R) = G(K)`. This module restates them as factorizations
`g = κ * p` with `κ` integral, the form consumed by the uniqueness theorem of
`GenericSpecialFixedPoint` and `SplitIntegralFrameUniqueness`.

## Declarations

* `exists_integral_mul_of_hasLeftIntegralCovering`: for `M : IntegralModel R K G` and a
  subgroup `H` with `HasLeftIntegralCovering M H`, every `g` is `κ * p` with
  `κ ∈ M.integralPoints` and `p ∈ H`.
* `exists_integral_mul_parabolic`: let `R` be a strictly Henselian Noetherian valuation
  domain with fraction field `K`, let `G.X.left` be affine, and let `M` be a model with
  `IsReductive M.group`. Let `χ` be a cocharacter of `M.group` and `lam` a cocharacter of
  `G` with `Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫ M.genericIso.hom =
  lam`. Then every `g : rationalPoints G` is `κ * p` with `κ ∈ M.integralPoints` and
  `p ∈ (Dynamic.parabolic lam).carrier (Over.mk (𝟙 _))`.
* `baseChangeUnramified_exists_integral_mul_parabolic`: the same factorization for
  `M.baseChangeUnramified`. Here `M : IntegralModel 𝒪[F] F G` is a model over a
  nonarchimedean local field, with `G` connected reductive and a connected reductive
  special fibre. The cocharacter `χ` of `M.baseChangeUnramified.group` must satisfy the
  corresponding equation `hlam` with `lam`.

## Implemented proof

For the first statement, apply the published `hasLeftIntegralCovering_iff` to `g⁻¹`. This
gives `g⁻¹ = p * κ` with `p ∈ H` and `κ` integral, so `g = κ⁻¹ * p⁻¹`. Both factors stay
in their subgroups. The other two statements rewrite the published
`hasLeftIntegralCovering_parabolic` and
`baseChangeUnramified_hasLeftIntegralCovering_parabolic` along `hlam` and then apply the
first.

## Provenance and scope

Internal restatement of published results (Getz–Hahn, Theorem B.2.5, in the
strictly Henselian form of `HenselianParabolicCovering`). It adds no mathematical
content. It does not produce the cocharacter `χ` from building data.
