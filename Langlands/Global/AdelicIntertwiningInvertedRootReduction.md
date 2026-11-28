# Restricted continuation of tested intertwining terms from the inverted-root continuation

Module `Langlands.Global.AdelicIntertwiningInvertedRootReduction` proves

`Langlands.Global.intertwiningRestrictedCuspidalTestContinuationReduction :
IntertwiningRestrictedCuspidalTestContinuationReductionStatement.{u}`,

where `IntertwiningRestrictedCuspidalTestContinuationReductionStatement` is the implication
`IntertwiningInvertedRootCuspidalTestContinuationStatement.{u} →
IntertwiningRestrictedCuspidalTestContinuationStatement.{u}`. The premise is defined in
`Langlands.Global.AdelicIntertwiningInvertedRootStatement`, the conclusion in
`Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningReduction`; see their Markdown for the
setting. The module does not prove the premise.

## Idea

For `I' ≤ I` with `f : P_{I'} → P_I` and a normalizer point `n` whose Weyl element `w` maps every
simple root in `I` to a positive root, `w` maps the positive roots of `M_I` to positive roots. So
every root `β > 0` inverted by `w` lies in `U_I`, and on restricted parameters `λ|`,
`λ ∈ X^*(P_I) ⊗ ℂ`, the root form of `β|_{A_{I'}}` is the root form of the root `β|_{A_I}` of `A_I` in
`U_I`. Restricting the continuation in parameters of `P_{I'}` with poles along the inverted roots
therefore gives a continuation in parameters of `P_I` with poles along root hyperplanes of `P_I`,
and restricted regular parameters of `P_I` are regular for the inverted roots, where the premise
gives agreement with the integral (Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2.2, Theorem 2.3 (3) and §8.6; Mœglin–Waldspurger,
*Spectral decomposition and Eisenstein series*, II.1.6 (iv)).

## Lemmas on roots and root forms

All are in the namespace `Langlands.Global.StandardParabolicFamily`, for a standard parabolic
family `𝓕` with maximal split torus `T` and generic cocharacter `ν`.

- `one_tmul_notMem_span_of_inverted`: if `schemeWeylCharacterAction 𝓕.i (mk n) α` is a positive
  relative root for every `α ∈ I`, `χ` is a positive relative root and its transport by `n` is
  not positive, then `1 ⊗ χ ∉ span_ℝ (1 ⊗ I)` in `X^*(T) ⊗ ℝ`. Proof: take a standard cocharacter
  `ζ` of `I` (`standardCocharacter`; it pairs to `0` with the simple roots in `I` and positively with
  the other simple roots). If `1 ⊗ χ` were in the span, the real pairing `pair T (·) (1 ⊗ ζ)` would
  vanish on it, so `⟨χ, ζ⟩ = 0`. By induction over the additive closure of the simple roots, every
  element `x` of it has `⟨x, ζ⟩ ≥ 0`, and `⟨x, ζ⟩ = 0` implies `⟨n · x, ν⟩ ≥ 0` (a simple root with
  zero pairing lies in `I`, and `n` maps it to a positive root). Since `χ` is in the closure
  (`DominantDisplacement.positive_mem_closure`), `⟨n · χ, ν⟩ ≥ 0`; as `n · χ` is a relative root
  (`schemeWeylCharacterAction_image_relativeRoots`) and `ν` is generic, `⟨n · χ, ν⟩ > 0`, so `n · χ`
  would be positive.
- `restrict_mem_unipotentRoots_of_notMem_span`: a positive root `χ` with `1 ⊗ χ ∉ span_ℝ (1 ⊗ I)`
  restricts to a root `χ ∘ f_I` of `A_I` in `U_I`, since the kernel of restriction to `A_I` is
  `span_ℝ (1 ⊗ I)` (`ker_restrictReal_splitComponent`).
- `torusRestrictReal_restrictReal`: for `f ≫ 𝓕.p I = 𝓕.p I'`, restricting a real parameter of
  `P_I` first to `P_{I'}` and then to `T` is restricting it to `T` (`torus_comp_factor`).
- `parameterRealPart_parameterRestrict`: the real part of `parameterRestrict f λ` is the
  restriction of the real part of `λ`.
- `realRootFunctional_restrictReal` and `rootFunctional_comp_parameterRestrict`: the root form of
  `χ ∘ f_{I'}` composed with restriction from `P_I` to `P_{I'}` is the root form of `χ ∘ f_I`, for
  real and complex parameters; both are `x ↦ B_T(x|_T, χ)` (`realRootFunctional_eq`).
- `re_rootFunctional`: the real part of `rootFunctional β λ` is `realRootFunctional β (Re λ)`.
- `rootFunctional_ne_zero`: the root form of a root of `A_I` in `U_I` is not zero, because it has
  positive real part at a point of the positive chamber (`positiveChamberNonempty`).
- `isInvertedRootRegular_parameterRestrict`: under the positivity hypothesis on `n`, if `λ` is
  `R`-regular for `P_I`, then `parameterRestrict f λ` is `R`-regular for the roots of `A_{I'}` in
  `U_{I'}` inverted by `n`: for an inverted root `β = χ ∘ f_{I'}`, the value
  `B(Re λ|_{A_{I'}}, β)` equals `B(Re λ|_{A_I}, χ ∘ f_I)`, and `χ ∘ f_I` is a root of `A_I` in `U_I`.

## The proof of the reduction

Given the premise and the data of the conclusion (`I`, `I'`, `J`, `f`, `n`, `c`, `π`, the
positivity hypothesis and `φ'`), the premise applied to `I'`, `J`, `n`, `c`, `π`, `φ'` gives `k`,
`Φ`, coefficients `coeff i` on `X^*(P_{I'}) ⊗ ℂ` with domain `D`, poles along the inverted roots, and
`R` with agreement on the parameters `R`-regular for the inverted roots, all of which lie in `D`.

1. For every inverted root `β` choose a positive lift `χ_β` with non-positive transport, and put
   `σ β = χ_β ∘ f_I`. By the lemmas above, `σ β` is a root of `A_I` in `U_I`, and with
   `τ = parameterRestrict f` the pulled-back form `rootFunctional_{I'} β ∘ τ` equals
   `rootFunctional_I (σ β)`, which is not zero.
2. `exists_comp_linearMap_of_hasRootHyperplanePoles` (module
   `Langlands.Analysis.Meromorphic.RootHyperplaneRestriction`), applied to each `coeff i` and `τ`
   (`X^*(P_I) ⊗ ℂ` is finite-dimensional by `rationalCharacters_free_finite`), gives `coeff' i` on
   `X^*(P_I) ⊗ ℂ`, meromorphic in coordinates with a domain `D' i`, with poles along the forms
   `rootFunctional_{I'} β ∘ τ`, and with `coeff' i λ = coeff i (τ λ)` whenever `τ λ ∈ D`.
3. The witnesses are `k`, `Φ`, `coeff'`, the domain `⋂ i, D' i` (open and dense in coordinates,
   `isOpenDenseInCoordinates_iInter_of_finite`; meromorphy by
   `IsMeromorphicInCoordinatesOn.congr_mono`), and the bound `R`. The pole condition for the root
   forms of `P_I` and the roots of `A_I` in `U_I` follows from step 1 by
   `HasRootHyperplanePoles.of_proportional` (with factor `1`) and `HasRootHyperplanePoles.mono`.
4. For `λ` `R`-regular for `P_I`, `τ λ` is `R`-regular for the inverted roots
   (`isInvertedRootRegular_parameterRestrict`), hence lies in `D`; the premise rewrites the test of
   the intertwining term at `τ λ` as `∑ i, coeff i (τ λ) * (test of [Φ i])`, and
   `coeff i (τ λ) = coeff' i λ`. The parameter of the twist is
   `weylParameter (𝓕.l I') c π (parameterRestrict f λ)` on both sides.
