# A normalized inverse-character functional on norm-ordered unramified principal series

Module `Langlands.Representation.Conductor.OrderedUnramifiedSphericalFunctional`, namespace
`Langlands.Conductor`. Part of the proof of `SphericalCorankOneFunctionalEquationStatement`.
Nothing here uses `PadicField`. All results hold over every nonarchimedean local
field `F` (`IsNonarchimedeanLocalField F`, any characteristic), with uniformizer `ϖ`, residue
cardinality `q`, and `ρ = principalSeries hϖ n hq z`, `f₀ = sphericalSection hϖ n hq z`.

## Statements

- `isOfWhittakerType_principalSeries hϖ n hq z ψ`: `I(z)` is of Whittaker type
  (`RankinSelberg.IsOfWhittakerType n (standardCharacter ψ n)`) for every `z` and every unitary
  additive character `ψ`. That is, `I(z)` is admissible and finitely generated, and its
  `ψ`-Whittaker functionals form a line.
- `exists_glInverseFunctional_ne_zero hϖ n hq z ψ`: `I(z)` has a nonzero inverse-character
  functional `ℓ : glInverseFunctionals ψ n ρ`.
- `glInverseFunctional_sphericalSection_ne_zero hϖ n hq z hmono hψ ℓ hℓ`: if the norms
  `‖z i‖` are nondecreasing (`Monotone`) and `ψ` has integer conductor, then every nonzero
  inverse-character functional `ℓ` on `I(z)` has `ℓ(f₀) ≠ 0`.
- `exists_glInverseFunctional_sphericalWhittaker hϖ n hq z hmono hψ`: under the same
  hypotheses there is `ℓ : glInverseFunctionals ψ n ρ` with `ℓ.val ≠ 0` and
  `(coefficientMap ρ ℓ f₀).val g = Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z g`
  for every `g`.

The last theorem is clauses 1 and 3 of the Library statement
`OrderedUnramifiedWhittakerRealizationStatement`. Clause 2 (injectivity of the coefficient
map, Jacquet–Shalika 1983, Proposition (3.2)) is not proved here and is not needed by the
corank-one functional equation.

## Proofs

1. Whittaker type. The all-field theorem
   `AllField.RankinSelberg.normalizedProductWhittakerType` (normalized product induction
   preserves Whittaker type) is applied to `n + 1` blocks of size one carrying the rank-one
   characters `χ_{z_i}` (`AllField.Conductor.UnramifiedPrincipalSeries.blocks`). Each block is
   of Whittaker type by `AllField.RankinSelberg.rankOneCharacter_isOfWhittakerType`.
   `IsOfWhittakerType.of_equiv` carries the result back to `I(z)` along the inverse of
   `AllField.Conductor.UnramifiedPrincipalSeries.principalSeriesEquiv`, which identifies
   `I(z)` with that induction.
2. A nonzero functional. `isOfWhittakerType_standard_iff_inverse` turns this into a linear
   equivalence `e` from the inverse-character functionals to `ℂ`. The functional `e⁻¹(1)` is
   nonzero because `e⁻¹` is injective.
3. Nonvanishing on `f₀`. Suppose `ℓ(f₀) = 0`. Shintani's formula
   `coefficientMap_sphericalSection_apply` (module `UnramifiedSphericalWhittaker`) gives
   `ℓ(ρ(g) f₀) = ℓ(f₀) · W(g) = 0` for every `g`. By Jacquet's Lemma 1, the published
   `orderedUnramifiedSphericalCyclicity`, `f₀` generates `I(z)` because the norms are
   nondecreasing. For any `v`, the published `exists_finset_translate_of_cyclic` therefore
   writes the coefficient of `v` as a finite combination of right translates of the coefficient
   of `f₀`. Evaluation at `1` gives `ℓ(v) = 0`. So `ℓ = 0`, a contradiction.
4. Normalization. Take `ℓ₀` from step 2 and let `c = ℓ₀(f₀)`, which is nonzero by step 3.
   Then `ℓ = c⁻¹ • ℓ₀` is nonzero. By Shintani's formula its coefficient of `f₀` is
   `c⁻¹ c · inverseSphericalWhittaker hψ.1 hϖ q z = inverseSphericalWhittaker hψ.1 hϖ q z`,
   whose values are `Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z` by
   definition.

## Provenance

The argument follows H. Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific J. Math. 260 (2012), §1, printed page 518: Lemma 1 (cyclicity of
`f₀` in the ordered case), together with uniqueness of Whittaker functionals and the
Shintani–Casselman–Shalika formula for the spherical coefficient. Existence of a nonzero
functional comes from Whittaker type of induced representations of Whittaker type
(Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105
(1983), Sections (2.1) and (2.3)), here through the all-field Library theorem. This route
avoids Lemma 2 (injectivity), which the corank-one functional equation does not use.
