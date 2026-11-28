# The family comparison under a change of presentation of the inducing parabolic

Module `Langlands.Global.AdelicEisensteinFamilySourceRange` proves that the family comparison
(module `Langlands.Global.AdelicEisensteinFamilyRegularComparison`) depends only on the image
of the inducing parabolic, its radical and its Levi, for presentations with the same torus,
chamber and simple roots. It also proves three facts on restriction of parameters.

## Restriction of parameters

For group schemes `H`, `H'`, `H''` over a field `F`:

- `parameterRestrict_id`: restriction of complex parameters `X^*(H) ⊗ ℂ → X^*(H) ⊗ ℂ` along
  `𝟙 H` is the identity.
- `parameterRestrict_comp g f`: restriction along `g ≫ f` is restriction along `f` followed by
  restriction along `g`.
- `parameterRestrictEquiv e`: for an isomorphism `e : H' ≅ H`, restriction along `e.hom` is a
  linear equivalence `X^*(H) ⊗ ℂ ≃ X^*(H') ⊗ ℂ` with inverse restriction along `e.inv`
  (`parameterRestrictEquiv_apply` is its formula).

The first two are proved by induction on tensors from `characterRestrict_id` and
`characterRestrict_comp`.

## Main theorem

`FamilyRegularComparison.of_sourceRange`: let `G` be connected reductive and `p₁ : P₁ → G`,
`p₂ : P₂ → G` parabolics with presentations `⟨T, i, ν, J, f₁⟩` and `⟨T, i, ν, J, f₂⟩`
(same torus, cocharacter and simple roots), identified by `e : P₂ ≅ P₁` with `e ≫ p₁ = p₂`. Assume
that `p₁`, `p₂` have the same image, the radicals `iU₁ ≫ p₁`, `iU₂ ≫ p₂` have the same image, the
Levis `l₁ ≫ p₁`, `l₂ ≫ p₂` have the same image, and the Weyl data correspond:
`weylParameter l₂ c₂ π' (e^* λ) = weylParameter l₁ c₁ π' λ` for every `λ`, where `e^*` is
restriction along `e`. If `K` has Iwasawa coverage for `P₁`, `P₂` and `Q`, then the family
comparison for `p₂` (with `c₂`) implies the family comparison for `p₁` (with `c₁`).

### Proof

Write `tr = parameterRestrictEquiv e`. The ingredients are:

- regularity: `λ` is `R`-regular for the first presentation if and only if `tr λ` is
  `R`-regular for the second (`eisensteinRegularityParabolicTransport`, module
  `Langlands.Global.AdelicEisensteinRegularityParabolicTransport`);
- the inducing spaces agree (`parabolicQuotientSubgroup_eq_of_range_eq`);
- `E_{P₁}(φ, λ) = E_{P₂}(φ, tr λ)` (`IsIwasawaCompact.eisensteinSeries_eq_of_range_eq`, module
  `Langlands.Global.AdelicEisensteinParabolicRangeTransport`);
- `M_{P₁}(w, λ)φ = M_{P₂}(w, tr λ)φ`, from the Weyl data hypothesis, the equality of parameter
  twists along `e` (`IsIwasawaCompact.parameterTwist_restrict_of_comp_eq`) and
  `IsIwasawaCompact.intertwiningIntegral_eq_of_range_eq_of_twist`.

The data for `p₂` are the same functions with coefficients, `EP`, and domains composed with
`tr.symm` (`IsMeromorphicInCoordinatesOn.comp_linearEquiv`). The comparison for `p₂` gives
coordinates `e₂` and a patch `O`. The coordinates `e₂.trans tr.symm` and the same `O` give the
conclusion for `p₁`, since the transported parameters agree by the Weyl data hypothesis.
