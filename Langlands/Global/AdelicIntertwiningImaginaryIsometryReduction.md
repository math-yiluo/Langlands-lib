# Reduction of the isometry at imaginary points of holomorphy

Module `Langlands.Global.AdelicIntertwiningImaginaryIsometryReduction` states
and proves

`IntertwiningImaginaryIsometryReductionStatement :=
IntertwiningContinuedAdjunctionStatement → IntertwiningCocycleStatement.{0} →
IntertwiningMeromorphicContinuationStatement.{0} →
IntertwiningImaginaryIsometryStatement`

(theorems `intertwiningImaginaryIsometry_of_inputs` and
`intertwiningImaginaryIsometryReduction`). Its target is
`IntertwiningImaginaryIsometryStatement`. It is a conditional
result: none of the three premises is proved in the Library. The cocycle
relation is stated in `Langlands.Global.AdelicIntertwiningCocycleStatement` and
the meromorphic continuation in
`Langlands.Global.AdelicIntertwiningContinuationStatement`; the adjunction statement is stated in
`Langlands.Global.AdelicIntertwiningAdjunctionStatement`. The universe `0`
matches the number fields `F : Type` of the target.

## Source

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`,
IV.3.12, p.161: from the adjunction relation
`⟨φ', M(w, λ)φ⟩ = ⟨M(w⁻¹, -wλ̄)φ', φ⟩` and the functional equation one obtains
`⟨M(w, λ)φ, M(w, λ)φ⟩ = ⟨φ, φ⟩` for imaginary `λ` where `M(w, ·)` is
holomorphic. The implemented proof follows this route and adds what the source
leaves implicit: the functional equation is derived from the cocycle relation
and `M(1, λ) = 1`; the identity is first obtained on a common open dense set
of parameters, on which all expansions, the functional equation and the
adjunction hold; and it is carried to the imaginary point by continuity of
the coefficients `coeff'` there. That set is not required either to meet or
to avoid the imaginary subspace.

## Helper declarations

- `Langlands.Analysis.Meromorphic.isMeromorphicInCoordinatesOn_iInter_fin`: a
  family `f : Fin k → X → ℂ` meromorphic with domain `D` is meromorphic with
  domain `⋂ _ : Fin k, D`, which is open and dense in coordinates (for `k = 0`
  it is the whole space, so empty families impose no condition).
- `isMeromorphicInCoordinatesOn_zero`: `0` is meromorphic with any domain open
  and dense in coordinates.
- `negConjHomeomorph n`: the homeomorphism `s ↦ -s̄` of `ℂⁿ`.
- `eq_of_continuousAt_of_dense`: a function continuous at `x` and equal to `c`
  on a dense set takes the value `c` at `x`.
- `IsMeromorphicInCoordinatesOn.continuousAt_comp`: in every linear chart, a
  function meromorphic in coordinates is continuous at the points of its domain
  of holomorphy.
- `combinedFamily`, `combinedCoeff`, `sum_combinedCoeff_mul`
  (namespace `Langlands.Global`): finitely many expansions
  `∑ t, b i t ν • χ i t` (`t < k i`) are rewritten over one family indexed by
  `Fin (∑ i, k i)` (through `finSigmaFinEquiv`), with the coefficients of the
  other families padded by `0`.
- `inducedInnerProduct_sum_sum`: for the integrand
  `AdelicGroupPoints.inducedInnerProductIntegrand` of `inducedInnerProduct` on
  `K × M(F) \ M(𝔸)` (defined in `Langlands.Global.AdelicIntertwiningAdjunctionStatement`),
  sesquilinearity
  `(∑ i, x i • f i, ∑ j, y j • h j)_P = ∑ i, ∑ j, x i · conj (y j) · (f i, h j)_P`
  whenever all pairwise integrands are integrable for the product of the Haar
  probability on `K` and the quotient measure (Fubini, `integral_prod`, and
  linearity of the product integral).
- `AdelicGroupPoints.IsWeylConjugation.inv`: if `(w, c)` presents an element of
  `W(P, Q)`, then `(w⁻¹, c⁻¹)` presents an element of `W(Q, P)`
  (`innerIso_inv_hom`).

## Proof of `intertwiningImaginaryIsometry_of_inputs`

Fix the data of the target, `coeff'` and `DM'`, `μ` with
`λ₀ = imaginaryParameter F P μ ∈ DM'`, and `j`, `j'`.

1. *Structure of `P`.* `G` is smooth, so the presentation `r` gives
   `IsIso (subgroupMultiplication l iU)` for the given radical
   (`ParabolicRootPresentation.isIso_subgroupMultiplication_of_radical`), and
   `π = leviRetraction l iU` is a retraction of `l`.
2. *Structure of `P'`.* The split component `a` of `M` is transported to `M'`
   along `cw⁻¹`, and `parabolicRootPresentationExistence` gives a presentation
   `r₁` of `P'` with this split component (as in the cocycle reduction). The
   pair `(w⁻¹, cw⁻¹)` presents the inverse Weyl element.
3. *Reverse expansions.* `IntertwiningMeromorphicContinuationStatement.{0}`,
   applied to each `ψ j' i ∈ A^2_{P'}` with `(w⁻¹, cw⁻¹)`, gives finite
   expansions of `M(w⁻¹, ν)(ψ j' i)` in automorphic forms on
   `U(𝔸)M(F) \ G(𝔸)`; they are combined into one family `χc` with
   coefficients `bc i x`, meromorphic on
   `Ec = ⋂ i, ⋂ _ : Fin (k i), E i`.
4. *Functional equation.* `IntertwiningCocycleStatement.{0}` with
   `Q = P'`, `Q'' = P`, `(w, cw)` and `(w⁻¹, cw⁻¹)` is applied to `v j'`: the
   composite expansion is `M(w⁻¹ w, λ)(v j') = v j'`, which is the published
   `IsIwasawaCompact.intertwiningOperator_one_self` of
   `Langlands.Global.AdelicIntertwiningIdentity` (with the presentation `r`
   and the retraction `π`) after `w⁻¹ * w = 1` and `cw⁻¹ ≫ cw = 𝟙 M`; left
   `U(𝔸)`-invariance of `v j'` comes from its automorphy. The conclusion is
   `∑ i, coeff j' i μ' · ∑ x, bc i x (wμ') · χc x = v j'` for
   `μ' ∈ ⋂ _ : Fin m, DM` with `wμ' ∈ Ec`.
5. *Adjunction.* `IntertwiningContinuedAdjunctionStatement` is applied to
   `φ = v j`, its expansion `(ψ j, coeff j)`, the family `ψ j'` and the combined
   reverse expansion; it provides an open dense `S₀ ⊆ ℂⁿ`.
6. *The Gram function.* In the chart `realChart e` let
   `G(s) = ∑ i, ∑ i', coeff' j i (λ_s) · conj (coeff' j' i' (λ_s*)) · (ψ j i, ψ j' i')_{P'}`
   with `λ_s = realChart e s` and `λ_s* = realChart e (-s̄) = -λ̄_s`. Let `S`
   be the set of `s ∈ S₀` with `λ_s`, `λ_s*` in
   `⋂ _ : Fin m, DM ∩ ⋂ _ : Fin m, DM'` and `wλ_s* ∈ Ec`. It is open and dense
   as a finite intersection of open dense sets: the domains are open and dense
   in the chart, `s ↦ -s̄` is a homeomorphism (`negConjHomeomorph`), and the
   preimage of `Ec` under `s ↦ wλ_s` is open and dense because `λ ↦ wλ` is a
   complex linear equivalence (the published
   `AdelicGroupPoints.exists_weylParameter_linearEquiv` of
   `Langlands.Global.AdelicWeylParameterEquivalence`). For `s ∈ S`:
   `G(s)` equals `(∑ i, coeff' j i λ_s · ψ j i, ∑ i', coeff' j' i' λ_s* · ψ j' i')_{P'}`
   by sesquilinearity (the pairwise integrands are integrable by
   `InducedInnerProductIntegrable.integrable_inducedInnerProduct_integrand`,
   using the transported split component of `M'`); the two functions equal the
   expansions with `coeff` by the agreement hypothesis on `DM ∩ DM'`; the
   adjunction with constants `coeff j' i' λ_s*` turns the pairing into
   `(v j, ∑ x, (∑ i', coeff j' i' λ_s* · bc i' x (wλ_s*)) · χc x)_P`; and by
   step 4 at `μ' = λ_s*` the second function is `v j'`. The integrability
   hypothesis of the adjunction for this combination is therefore the
   integrability of the integrand of `(v j, v j')_P`, which holds because both
   forms are in `A^2_P` (`integrable_inducedInnerProduct_integrand`, with the
   split component of `r` and the retraction `π`). So `G = (v j, v j')_P` on
   `S`.
7. *Continuity at the imaginary point.* Let `s₀ = (realChart e)⁻¹ λ₀`. Its
   coordinates are purely imaginary (`realChart_symm_imaginary_re`), so
   `-s̄₀ = s₀`. Every `coeff' j i ∘ realChart e` is holomorphic, hence
   continuous, at `s₀` because `λ₀ ∈ DM'`, and so is
   `s ↦ coeff' j' i' (realChart e (-s̄))`. Thus `G` is continuous at `s₀`,
   and `eq_of_continuousAt_of_dense` gives `G(s₀) = (v j, v j')_P`, which is
   the target identity since `λ_{s₀} = λ_{s₀}* = λ₀`.

The set `S` carries no condition relative to the imaginary subspace: it need
neither meet it nor avoid it. Only density of `S` and continuity of the
coefficients `coeff'` at `λ₀ ∈ DM'` are used, so the argument also covers
`n = 0`, where the chart is a point and the imaginary subspace is everything.
The forward expansions `coeff` and the reverse expansions need not be regular
at `λ₀`.

## Scope

The theorem is conditional on the three premises. It does not use
`InducedInnerProductGramStatement` or the root-hyperplane statement, and it
proves neither holomorphy of `M(w, ·)` on the imaginary axis nor the
adjunction, cocycle or continuation statements.
