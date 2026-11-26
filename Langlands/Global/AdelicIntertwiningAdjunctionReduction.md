# Reduction of the adjunction of continued intertwining operators

Module `Langlands.Global.AdelicIntertwiningAdjunctionReduction`. Its target is the Library's
`Langlands.Global.IntertwiningContinuedAdjunctionStatement` (module
`Langlands.Global.AdelicIntertwiningAdjunctionStatement`): Mœglin–Waldspurger II.1.8 and
IV.1.9 (e), the adjunction `(M(w, λ)φ, φ')_{P'} = (φ, M(w⁻¹, -wλ̄)φ')_P` of continued
intertwining operators.

This module states two results, each with its own source, and proves that together they imply
the target (`intertwiningContinuedAdjunction_of_inputs`). It proves neither of them. All
declarations named without a namespace below are in `Langlands.Global`.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  Tracts in Math. 113 (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`:
  - II.1.6, Proposition (i) and (iv), printed pp.87–89 (chapter file
    `06.1_pp_78_100_Definitions.pdf`): the intertwining integral
    `∫_{(U'(k) ∩ wU(k)w⁻¹) \ U'(𝔸)} φ_π(w⁻¹ u g) du` converges absolutely and uniformly for `g`
    in a compact set when `⟨Re π, α^∨⟩ ≫ 0` for the simple roots of `G` relative to `M`
    (part (i)); part (iv) weakens the condition to the roots `α > 0` with `wα < 0`.
  - II.1.8, "Adjunction of intertwining operators", printed pp.93–94 (same chapter file):
    for cuspidal data and `Re π` in the positive cone of absolute convergence,
    `⟨φ', M(w, π)φ⟩ = ⟨M(w⁻¹, -wπ̄)φ', φ⟩`, proved by unfolding the integral along
    `(U'(k) ∩ wU(k)w⁻¹) M'(k) Z \ G`.
  - IV.1.9 (e), printed p.140 (chapter file `08.1_pp_135_141_The_results.pdf`): "The
    adjunction formula II.1.8 can be continued to an equality of meromorphic functions."
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`,
  §2.2, p.191 (TeX `1911.02342.tex` lines 432–437): the integral defining `M(w, λ)` "converges
  locally uniformly in `g` and `λ` provided that `⟨Re λ, α^∨⟩ ≫ 0` for every root `α ∈ Φ_P`
  such that `wα < 0`".

## `IntertwiningConvergentAdjunctionStatement`

The binders and hypotheses are those of `IntertwiningContinuedAdjunctionStatement` up to the
weights `β`, `β'`, in the same order (see the Markdown of that statement): a number field `F`,
connected reductive `G`, parabolics `P = MU` and `P' = M'U'` with presentations `r`, `r'` and
Levi retractions `π`, `π'`, a pair `(w, cw)` with `IsWeylConjugation p l p' l' w cw` and `cw'`
with `IsWeylConjugation p' l' p l w⁻¹ cw'`, a maximal compact `K` with `P(𝔸)K = P'(𝔸)K = G(𝔸)`,
a closed matrix embedding `rho` with the smooth-structure data, Iwasawa-compatible Haar
measures `μM`, `μM'`, coordinates `e` and `e' = w ∘ e`, and continuous compactly supported
weights `β`, `β'` of integral `1`. These define `(·,·)_P = inducedInnerProduct K hK.isCompact p
l μM e β` and `(·,·)_{P'} = inducedInnerProduct K hK'.isCompact p' l' μM' e' β'`. Then for
`φ ∈ A^2_P` and `φ' ∈ A^2_{P'}` (`IsSquareIntegrableInducedForm`) there is `R` such that for
every `s ∈ ℂⁿ` with `λ = realChart e s` `R`-regular (`r.IsRegularParameter hA hT R λ`), writing
`ν = weylParameter l cw π' (realChart e (-conj s))`, which is `-wλ̄`:

1. the integrand `AdelicGroupPoints.inducedInnerProductIntegrand` of `(M(w, λ)φ, φ')_{P'}` is
   integrable on `K × M'(F) \ M'(𝔸)`;
2. the integrand of `(φ, M(w⁻¹, ν)φ')_P` is integrable on `K × M(F) \ M(𝔸)`;
3. `(M(w, λ)φ, φ')_{P'} = (φ, M(w⁻¹, ν)φ')_P`.

Here `M(w, λ)` is `hK.intertwiningOperator hK' iU l iU' cw π' w` and `M(w⁻¹, ν)` is
`hK'.intertwiningOperator hK iU' l' iU cw' π w⁻¹`: both are the intertwining integrals, not
continuations.

Correspondence with the source.

- The region. For `α > 0` a root of `A_M` in `U` with `wα < 0`, `wα = -α'` for a root `α'` of
  `A_{M'}` in `U'` with `w⁻¹α' < 0`, and `⟨-w Re λ, α'^∨⟩ = ⟨Re λ, α^∨⟩`. So `ν = -wλ̄` lies in
  the cone of II.1.6 (iv) for `w⁻¹` exactly when `λ` lies in the cone for `w`; for `R`-regular
  `λ` and `R` large both integrals converge (II.1.6 (iv)), which is MW's "positive cone of
  absolute convergence".
- The identity is II.1.8 in the Library's normalization of `M(w, λ)` (Bernstein–Lapid §2.2:
  `[M(w, λ)φ]_{wλ}` is the intertwining integral), in which `M(w, λ)φ` and `φ'` have the same
  equivariance under the split component and `(·,·)_{P'}` is Lapid's quotient integral; the
  Markdown of `IntertwiningContinuedAdjunctionStatement` explains the conjugation in the chart,
  the measures and why `P`, `P'` need not be standard and `K` need not be in good position.
- Data. MW state II.1.8 for cuspidal data. The statement is for `φ ∈ A^2_P` and
  `φ' ∈ A^2_{P'}`, as `IntertwiningContinuedAdjunctionStatement` is, and asserts the
  integrability of both integrands. For cuspidal data it is part of MW's proof ("Each integral
  converges absolutely"); for forms of the discrete spectrum it holds because the operators map
  `A^2` to `A^2` (Lapid 2011, §2, p.312, Working hypothesis, for standard parabolics and `K` in
  good position).

## `IntertwiningReflectedRegionAgreementStatement`

The binders are those of `IntertwiningMeromorphicContinuationStatement` (module
`Langlands.Global.AdelicIntertwiningContinuationStatement`), with a presentation
`r' : ParabolicRootPresentation q l' a'` of `Q = M'V` in place of the hypotheses
`IsParabolicSubgroup q`, `IsRationalLeviSubgroup l'` and `IsIso (subgroupMultiplication l' iV)`,
which follow from `r'` and the hypothesis on `iV`: a number field `F` (in any universe),
connected reductive `G`, `P = MU` with presentation `r`, `Q = M'V` with presentation `r'` and a
retraction `π'` of `l'`, `(w, c)` with `IsWeylConjugation p l q l' w c`, a maximal compact `K`
with `hK`, `hK'`, a closed matrix embedding `rho` and `φ` automorphic on `U(𝔸)M(F) \ G(𝔸)`. Take
functions `ψ i` on `G(𝔸)` and coefficients `coeff i`, meromorphic in linear coordinates with one
domain `D`, such that `M(w, λ)φ = ∑ i, coeff i λ • ψ i` for `Re λ` sufficiently regular
(`r.IsRegularParameter hA hT R₀ λ`). The conclusion: there is `R` such that for every `λ ∈ D`
with `-wλ` `R`-regular for `r'` (`r'.IsRegularParameter hA' hT' R (-weylParameter l c π' λ)`),
and every `g`, the intertwining integral `M(w, λ)φ(g)` equals `∑ i, coeff i λ * ψ i g`.

Correspondence with the source.

- The region. If `-wλ` is `R`-regular for `r'` then, by the computation above (with `Q` in place
  of `P'`), `⟨Re λ, α^∨⟩` is bounded below in terms of `R` for every root `α` of `A_M` in `U` with
  `wα < 0`. So for large `R` these `λ` lie in the cone of MW II.1.6 (iv) and BL §2.2, where the
  integral converges locally uniformly in `g` and `λ` and is therefore holomorphic in `λ`. The
  cone is a convex tube; it also contains the sufficiently regular `λ` of the hypothesis. The
  two functions `λ ↦ M(w, λ)φ(g)` and `λ ↦ ∑ i, coeff i λ * ψ i g` agree there, hence (identity
  theorem) on the part of the cone in `D`. The statement records this consequence of the cited
  convergence for the region where `-wλ` is regular, which is disjoint in general from the
  region where `λ` is regular (for instance for `w = 1`).
- The `ψ i` are arbitrary functions: for each `g` the right side is a meromorphic function of
  `λ`, which is all that the identity uses.

## `IntertwiningContinuedAdjunctionReductionStatement` and its proof

`IntertwiningContinuedAdjunctionReductionStatement` is the implication
`IntertwiningConvergentAdjunctionStatement → IntertwiningReflectedRegionAgreementStatement.{0} →
IntertwiningContinuedAdjunctionStatement`; `intertwiningContinuedAdjunctionReduction` proves it
by `intertwiningContinuedAdjunction_of_inputs`. The proof gives the conclusion of
`IntertwiningContinuedAdjunctionStatement` with `S = ℂⁿ`, that is, at every `s` with `λ ∈ D` and
`ν ∈ D'` at which the right-hand integrand is integrable.

1. *Domains.* `Dt = ⋂ _ : Fin k, D` and `D't = ⋂ _ : Fin m × Fin k', D'` are domains of
   holomorphy of the forward and reverse coefficients, open and dense in coordinates, and equal
   to the whole space for empty families (`isMeromorphicInCoordinatesOn_iInter_finite`).
2. *Thresholds.* `R₁` comes from the forward expansion, `R₂ i'` from the convergent adjunction
   for `φ` and `φ' i'`, and `R₃ i'` from the agreement statement applied to `(w⁻¹, cw')`, from
   `P'` (presentation `r'`) to `P` (presentation `r`), with `φ' i'`, its expansion and the domain
   `⋂ _ : Fin k', D'`. Let `R` exceed all of them. Since some parameter is `0`-regular
   (`ParabolicRootPresentation.exists_regularParameter`), the `R`-regular `s` contain a nonempty
   open set `O` (`exists_isOpen_isRegularParameter`).
3. *The identity on `O`.* Let `s ∈ O` with `ν ∈ D't`. By `weylParameter_weylParameter_of_inv`
   (from `weylParameter_comp`, `cw' ≫ cw ≫ l = l` and `weylParameter_one_self`),
   `-w⁻¹ν = realChart e (conj s)`, whose real part is that of `λ` (`parameterRealPart_realChart`);
   so it is `R₃ i'`-regular (`isRegularParameter_of_parameterRealPart_eq`) and the agreement
   statement identifies the integral `M(w⁻¹, ν)(φ' i')` with `∑ x, coeff' i' x ν * χ x`. The
   function `∑ x, (∑ i', c i' * coeff' i' x ν) * χ x` is then `∑ i', c i' * M(w⁻¹, ν)(φ' i')`.
   The convergent adjunction gives the integrability of each `(φ, M(w⁻¹, ν)(φ' i'))_P` integrand
   and `(φ, M(w⁻¹, ν)(φ' i'))_P = (M(w, λ)φ, φ' i')_{P'}`, and `M(w, λ)φ = ∑ i, coeff i λ * ψ i`.
   Sesquilinearity (`inducedInnerProduct_sum_right`, `inducedInnerProduct_sum_left`, and
   `inducedInnerProduct_sum_sum` with the integrability of products of forms in `A^2_{P'}`,
   `InducedInnerProductIntegrable.integrable_inducedInnerProduct_integrand`) gives, for every
   `c`, the integrability of the right-hand integrand and the identity of the conclusion.
4. *A conjugate-linear form.* `exists_inducedInnerProduct_sum_right_eq` gives `ℓ` with
   `(φ, ∑ x, a x • χ x)_P = ∑ x, conj (a x) * ℓ x` whenever the integrand is integrable. Its
   proof: the coefficient vectors with integrable integrand form a subspace of `ℂ^{k'}`, on
   which the pairing (an integral over the product, `inducedInnerProduct_eq_integral_prod`) is
   conjugate-linear; compose it with a projection onto that subspace along a complement.
5. *Two meromorphic functions on `ℂⁿ`.* `f₁ c s = ∑ i, coeff i λ * ∑ i', conj (c i') *
   (ψ i, φ' i')_{P'}` is meromorphic with domain `(realChart e)⁻¹ Dt`;
   `f₂ c s = ∑ x, ∑ i', conj (coeff' i' x ν) * (conj (c i') * ℓ x)` is meromorphic with domain
   the preimage of `D't` under `s ↦ ν`, because `s ↦ conj (f (-s̄))` is meromorphic for
   meromorphic `f` (`IsMeromorphicOn.conj_comp_negConj`, from
   `differentiableAt_conj_comp_negConj`). The left side of the conclusion is `f₁ c s` for every
   `s`, and the right side is `f₂ c s` wherever its integrand is integrable.
6. *Continuation.* By step 3, `f₁ c = f₂ c` on `O` where both are holomorphic, so by the identity
   theorem `IsMeromorphicOn.eq_of_eqOn_isOpen` they agree wherever both are holomorphic. This is
   MW IV.1.9 (e) in the form required by the target.

## Other declarations

- `Langlands.Analysis.Meromorphic.differentiableAt_conj_comp_negConj`: if `f : ℂⁿ → ℂ` is complex
  differentiable at `-s̄`, then `s ↦ conj (f (-s̄))` is complex differentiable at `s`; its
  derivative is `v ↦ conj (f'(-v̄))`, obtained from the real derivative by
  `hasFDerivAt_of_restrictScalars`.
- `Langlands.Analysis.Meromorphic.IsMeromorphicOn.conj_comp_negConj` and
  `Langlands.Analysis.Meromorphic.isMeromorphicInCoordinatesOn_iInter_finite`, used above.
- `Langlands.Global.AdelicGroupPoints.parameterRealPart_smul_realToComplexParameter` and
  `parameterRealPart_realChart`: the real part of `realChart e z` is `e (Re z)`.
- `Langlands.GroupScheme.ParabolicRootPresentation.isRegularParameter_of_parameterRealPart_eq`:
  regularity depends only on the real part.
- `Langlands.Global.AdelicGroupPoints.weylParameter_weylParameter_of_inv`: for Weyl conjugations
  `(w, cw)` and `(w⁻¹, cw')` and Levi retractions, `w⁻¹(wλ) = λ`.
- `inducedInnerProductIntegrand_add_right`, `inducedInnerProductIntegrand_mul_right`,
  `inducedInnerProductIntegrand_sum_right`, `inducedInnerProductIntegrand_sum_left`: linearity of
  the integrand of `(·,·)_P`.

## Provenance

The two statements are internal formulations, in the Library's coordinates and with its
intertwining integrals and inner products, of MW II.1.8 (with II.1.6) and of the agreement of
the continuation with the integral on the cone of II.1.6 (iv) and BL §2.2, as explained above.
The proof of the reduction is internal; its continuation step follows MW IV.1.9 (e) and uses the
identity theorem for meromorphic functions of several variables.

## Scope

The module proves neither `IntertwiningConvergentAdjunctionStatement` nor
`IntertwiningReflectedRegionAgreementStatement`. It asserts nothing about the convergence of
intertwining integrals or about square-integrability beyond these two statements.
