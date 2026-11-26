# Finite meromorphic expansions with root factorizations

Module `Langlands.Analysis.Meromorphic.RootFactorizedExpansion`. It contains definitions and
proved lemmas only, about families `μ ↦ Op μ` of scalar functions on a set `Gp`, parametrized
by finite-dimensional complex vector spaces, and their finite expansions. It builds on the
module `Langlands.Analysis.Meromorphic.RootFactorization`.

## Provenance (derived)

This is the bookkeeping of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §8.6, pp. 225–226 (registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`): the intertwining operators take
values in finite-dimensional spaces (Theorem 2.3 (3), p. 191), they compose (Theorem 2.3 (5)),
and the operator of an elementary symmetry depends on one coroot coordinate. Expanded in
finite bases, the coefficients of a composite are sums over paths of products of the
coefficients of the factors. The lemmas below state this for abstract families. The regions
`Reg R₀` stand for the regions of sufficiently regular parameters, and the predicates `Aut` for
automorphy.

## Linear algebra

- `exists_fin_linearIndependent_subfamily`: a family `f : Fin K → V` of vectors of a complex
  vector space has a linearly independent subfamily `f ∘ σ`, `σ : Fin k → Fin K`, in terms of
  which every `f i` is a linear combination (Mathlib's `exists_linearIndependent'`, with the
  finite index type enumerated).
- `coeff_eq_of_linearIndependent`: coefficients along a linearly independent finite family of
  scalar functions are unique.
- `sum_mul_eq_sum_of_expansion`: if `f j = ∑ s, A j s • e s` for all `j`, then
  `∑ j, x j * f j g = ∑ s, (∑ j, x j * A j s) * e s g`.
- Auxiliary: `Langlands.Global.isOpenDenseInCoordinates_univ`, `IsOpenDenseInCoordinates.preimage_linearEquiv`,
  `IsMeromorphicInCoordinatesOn.mul_const'`, `isMeromorphicInCoordinatesOn_sum'`,
  `IsMeromorphicInCoordinatesOn.mono'`.

## Expansions

- `HasMeromorphicExpansion Reg Aut Op`: there are `k`, functions `χ i` satisfying `Aut`,
  coefficients `coeff i` meromorphic in linear coordinates with one domain `D`, and `R₀` with
  `Op μ g = ∑ i, coeff i μ * χ i g` whenever `Reg R₀ μ`. This is the shape of the conclusion
  of `Langlands.Global.IntertwiningMeromorphicContinuationStatement`.
- `HasRootFactorizedExpansion L R Reg Aut Op`: the same with `D` open and dense in
  coordinates and every `coeff i` having a root factorization on `D`
  (`HasRootFactorizationOn L R D`).
- `HasMeromorphicExpansion.exists_openDense`: the domain can be taken open and dense in
  coordinates (if there is no coefficient, replace it by the whole space).
- `hasRootFactorizedExpansion_of_eq`: a family that does not depend on the parameter,
  `Op μ = ψ` with `Aut ψ`, has the root factorized expansion with the single function `ψ` and
  the constant coefficient `1`.
- `exists_merged_expansion`: finitely many families `S i` with expansions have expansions
  along one common family (the concatenation of the families, indexed through
  `finSigmaFinEquiv`, with coefficient `0` outside the block of `i`) and one common domain
  (the intersection of the domains).

## The composition step: `HasRootFactorizedExpansion.step`

Data: parameter spaces `X`, `Y`, a linear isomorphism `We : X ≃ₗ[ℂ] Y`, a linear form `α` on
`Y`, regions `RegX`, `RegY` (with `RegY` monotone in the bound), predicates `Aut₁`, `Aut₂` and
families `Op₀`, `Op₁ : X → Gp → ℂ`, `S : Y → (Gp → ℂ) → Gp → ℂ`. Hypotheses:

1. for every `R₀` and `ν` some chart contains a nonempty open set of points `s` with `e s` and
   `e s + ν` both in `RegY R₀`;
2. some `β ∈ R` has `L β ν = 0 → α (We ν) = 0`;
3. `Op₀` has a root factorized expansion with functions satisfying `Aut₁`;
4. for every `ψ` with `Aut₁ ψ`, `μ ↦ S μ ψ` has an expansion with functions satisfying `Aut₂`;
5. for every such `ψ` there is `R₀` with `S (μ + ν) ψ = S μ ψ` whenever `μ` and `μ + ν` lie in
   `RegY R₀` and `α ν = 0`;
6. `Op₁` has an expansion with functions satisfying `Aut₂`;
7. the composition rule: for every expansion `(χ, a, D)` of `Op₀`, every family of expansions
   `S μ (χ i) = ∑ j, b i j μ • ξ j` with one domain `D'`, and every expansion `(ζ, c, D'')` of
   `Op₁`, one has `∑ j, c j x * ζ j g = ∑ i, a i x * ∑ j, b i j (We x) * ξ j g` for
   `x ∈ D ∩ D''` with `We x ∈ D'`. This is the shape of the conclusion of
   `Langlands.Global.IntertwiningCocycleStatement`.

Conclusion: `Op₁` has a root factorized expansion with functions satisfying `Aut₂`.

Proof, as implemented:

1. Take the expansion `(χ, a, D)` of `Op₀`. Merge expansions of the `S μ (χ i)`
   (`exists_merged_expansion`), then replace the common family `ξ` by a linearly independent
   subfamily `ξ ∘ σ`, re-expanding the coefficients (`b₁ i s = ∑ j, b i j * A₁ j s`).
2. Invariance of `b₁ i s` under the kernel of `α`: for `α ν = 0`, take the open set of
   hypothesis 1 for the larger of the two bounds. At its points the two expansions of
   `S (μ + ν) (χ i) = S μ (χ i)` have equal coefficients by linear independence. The identity
   principle `translate_invariant_of_open` extends `b₁ i s (x + ν) = b₁ i s x` to the domain
   `D'`. Hence `b₁ i s` is a root factor on `D'` for the single form `α`, and by hypothesis 2
   and `IsRootFactorOn.comp_linearEquiv`, `b₁ i s ∘ We` is a root factor on `We ⁻¹' D'` for
   `L` and `R`.
3. Take the expansion `(ζ, c, D'')` of `Op₁` and apply the composition rule.
4. Choose a linearly independent subfamily `Φ ∘ τ` of the concatenation `Φ` of `ζ` and
   `ξ ∘ σ`. The new coefficients are `c₂ v = ∑ j, c j * A₂ j v`. They are meromorphic with
   domain `D''`, so also with the smaller domain `Dn = D ∩ D'' ∩ We ⁻¹' D'`, and they give
   `Op₁` on the regular region. The functions `Φ (τ v)` are among the `ζ j` and `ξ (σ s)`, so
   they satisfy `Aut₂`.
5. On `Dn`, the composition rule and linear independence of `Φ ∘ τ` give
   `c₂ v x = ∑ i, ∑ s, a i x * ((b₁ i s ∘ We) x * A₂ (natAdd s) v)`. The right side has a root
   factorization on `Dn` by the closure lemmas of `RootFactorization`: `a i` by hypothesis 3
   restricted to `Dn`, the root factors of step 2 restricted to `Dn`, and constants.

## Final assembly: `exists_rootFactorization_of_combination`

Data: a linear isomorphism `iota : X ≃ₗ[ℂ] X₀` such that for every `R'` some `R''` has
`RegX R'' λ → Reg₀ R' (iota λ)`, and such that each allowed form `L₀ β₀` on `X₀` pulls back to
a form vanishing on the kernel of some allowed `L β`; coefficients `E j` entire in coordinates,
functions `h j` on `Gp`, maps `τ j : Gp → Gp`, and families `Op j` on `X₀` with root
factorized expansions. If `T λ g = ∑ j, E j λ * h j g * Op j (iota λ) (τ j g)` on a region of
`RegX`, then `T` has an expansion on a region of `RegX`, with meromorphic coefficients on one
domain `D`, and these coefficients agree on `D` with `∑ j, ∏ t, fac i j t` for root factors
`fac i j t` on `D` with common numbers of summands and factors.

Proof: the functions are `g ↦ h j g * χ j i (τ j g)` and the coefficients
`λ ↦ E j λ * a j i (iota λ)`, indexed through `finSigmaFinEquiv`. The domain is
`D = ⋂ j, iota ⁻¹' D j`. The bound is the maximum of the bound for `T` and the sum of the
absolute values of the bounds `R''` that make `iota λ` regular for the expansion of each
`Op j`. Each coefficient has a root factorization: `E j` is a root factor, and `a j i ∘ iota`
has a root factorization by `HasRootFactorizationOn.comp_linearEquiv`. Common lengths come
from `exists_uniform_rootFactorization`.
