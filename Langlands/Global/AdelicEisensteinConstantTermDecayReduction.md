# Decay of Eisenstein series minus their constant term, from uniform growth and exponents

Module `Langlands.Global.AdelicEisensteinConstantTermDecayReduction`. It defines, in namespace
`Langlands.Global`,

- `EisensteinConstantTermDecayReductionStatement`, the implication
  `EisensteinUnitaryUniformGrowthStatement → EisensteinUnitaryExponentStatement →
  EisensteinConstantTermDecayStatement`,

and proves it:

```
theorem eisensteinConstantTermDecayReduction : EisensteinConstantTermDecayReductionStatement
```

It is a reduction. The two premises are stated in the modules
`Langlands.Global.AdelicEisensteinUnitaryGrowthStatement` (uniform moderate growth of `E(φ, λ)`
on compact sets of unitary parameters, Bernstein–Lapid 2024 with Lapid 2011, Proposition 6) and
`Langlands.Global.AdelicEisensteinUnitaryExponentStatement` (subunitary shift equations of order
`m` for the constant terms of `E(φ, λ)` along every standard parabolic, Lapid 2011,
Proposition 4, (13) and Lemma 6); this module does not prove them. They are the same two
Eisenstein inputs from which `eisensteinUniformTemperedness_of_criterion` (module
`Langlands.Global.AdelicEisensteinUniformTemperednessReduction`) derives Delorme's
Proposition 4.1. The conclusion is the statement of
`Langlands/Global/AdelicEisensteinConstantTermDecayStatement.lean`, unchanged.

The supporting results are in namespace `Langlands.Global.ConstantTermDecay`. The proof uses only
the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands` (published PDF numbering): §3.1, pp.10–11,
  Lemma 3.1 (the variant of Mœglin–Waldspurger, Lemma I.2.10, for a standard parabolic `Q`,
  with `β_Q = inf_{α ∉ J} α`); §4.2, p.17, Proposition 4.1 (bounds `(1 + ‖X‖)^n e^{ρ(X)}` for
  all derivatives `R_u E`, uniformly for `λ` in a compact subset of `i𝔞_P^*`); §5.1, p.19, proof
  of Lemma 5.1, where Lemma 3.1 bounds `φ − φ_Q`.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.2.10, printed pp.30–34
  (the estimate for a proper maximal standard parabolic and its omitted simple root, from
  bounds for finitely many derivatives) and I.2.11, printed p.34 (the maximal-parabolic
  estimates combined over the standard parabolics for the alternating sum of constant terms).

## How the proof follows the sources

Delorme applies Lemma 3.1 to `E(φ, λ)` with the bounds of Proposition 4.1 for the finitely many
derivatives that the lemma requires, and evaluates the result on Siegel sets. The implemented
proof has the same two ingredients, obtained from Library results:

- **Bounds for the derivatives.** The derivative words `D_s E(i e(x))` (right-orbit derivatives
  along a word `s` in a basis of the archimedean tangent space) form again a family with uniform
  moderate growth, and their constant terms satisfy the same shift equations. The Library's
  induction over standard parabolics, `StandardParabolicFamily.constantTerm_chamber_bound`
  (module `Langlands.Global.AdelicUniformTemperednessInduction`), applied to this family, gives
  the bound `C (2m ‖u‖ + 3)^{2m} δ_T(u)^{1/2}` for every derivative word of length `n` of every
  constant term `C_{J'} E`. The exponent `2m` does not depend on `n`, as in Delorme's spaces
  `ℱ_{Λ, ρ, n}`, whose polynomial exponent is the same for all derivatives `R_u`.
- **The decay along `Q`.** For a simple root `α` and a standard index `J''`, the step
  `C_{J''} E − C_{J'' ∖ α} E` has vanishing constant term along the maximal parabolic omitting `α`.
  The Library's form of Mœglin–Waldspurger I.2.10,
  `StandardParabolicFamily.exists_constantTermStep_decay` (module
  `Langlands.Global.AdelicUniformTemperednessDecay`), bounds the step at `b ω` by
  `C |α(b)|^{-n/[F:ℚ]}` times a bound for its derivatives of order `n` at the points `b k'`,
  `k'` in a larger compact set. The difference `E − E_Q` is the sum of such steps along a chain
  of standard indices from `Δ` down to `J`, removing one root `α ∉ J` at a time (a telescoping
  sum; I.2.11 combines the same maximal-parabolic estimates for the alternating sum of constant
  terms). With `n = k [F:ℚ]` each step gains `|α(b)|^{-k} ≤ e^{-k s}`.

The derivative bounds are evaluated at the same torus point `b` as the step, so the factor
`δ(b)^{1/2}` and the polynomial factor pass through the decay estimate unchanged.

## Supporting results

Derivative words (`adelicIteratedDirectionalValue`):

- `adelicIteratedDirectionalValue_mul_ofFinite`: right invariance under a subgroup of
  `G(𝔸_f)` passes to derivative words.
- `adelicIteratedDirectionalValue_leftMul`: `D_s (f(c ·))(x) = (D_s f)(c x)`.
- `contMDiff_adelicIteratedDirectionalValue`, `contMDiff_leftMul`: derivative words and left
  translates of a function smooth on the archimedean slices are smooth on the slices.
- `adelicIteratedDirectionalValue_sum`: on functions smooth on the archimedean slices, derivative
  words are linear on finite combinations `∑_i c_i f_i`. The proof realizes `D_s` on each slice
  as a ℂ-linear endomorphism of the smooth functions on `G(F_∞)`
  (`manifoldSmoothFunctions`), as in the Library's `adelicIteratedDirectionalValue_sub`.
- `isTranslationPolynomialSolution_adelicIteratedDirectionalValue`: if
  `∑_k c_k φ(a^k g) = 0` for all `g` and `φ` is smooth on the slices, then the same holds for
  `D_s φ`, by linearity and the commutation with left translation.
- `subgroupConstantTerm_adelicIteratedDirectionalValue`: for a smooth connected unipotent closed
  subgroup `U` and `f` continuous, smooth on the slices, left `U(F)`-invariant and right
  invariant under an open subgroup of `G(𝔸_f)`, every `D_s f` has the same four properties and
  `CT_U (D_s f) = D_s (CT_U f)`. Induction on `s`, using
  `adelicUnipotentConstantTermDifferentiation` for one derivative at a time.

The family of derivative words:

- `wordFamily hG hcalc f (x, s) = u_s · f x`, where `u_s = adelicDirectionalWordEnveloping hG s`
  is the ordered product of the enveloping generators of `s`; its underlying function is
  `D_s (f x)` (`evaluate_wordFamily`).
- `isUniformGrowthFamily_wordFamily`: for a finite set `Sw` of words, `wordFamily` has uniform
  moderate growth on `S ×ˢ Sw` with the same exponent and level as `f` on `S`. The level is
  preserved because the enveloping action commutes with finite right translations
  (`finitePlotSmoothEnvelopingAction_finiteRightAction`); the growth bound for `u · u_s · f x`
  is that of `(u u_s) · f x`, and one constant serves for the finitely many `s`.
- `hasSubunitaryShiftEquations_adelicIteratedDirectionalValue`: subunitary shift equations of
  order `m` pass from a function smooth on the slices to its derivative words, with the same
  roots `w_k`.
- `family_regularity`: for a family with uniform moderate growth, the slice smoothness and level
  of `f x`, the slice smoothness of the constant terms `C_Q (f x)` along standard parabolics, and
  `C_Q (D_s f x) = D_s (C_Q f x)`.
- `derivative_chamber_bound`: let `rho` have size `N > 0`, let `f` have uniform moderate growth
  on `S` and let the constant terms of every `f x` satisfy subunitary shift equations of order
  `m` along every standard index. For every `n`, standard index `J`, compact `Ω` and `θ ≥ 0` there
  is `C ≥ 0` with
  `‖D_s (C_J f x)(t ϖ)‖ ≤ C (2m ‖t‖ + 3)^{2m} δ_T(t)^{1/2}` for `x ∈ S`, words `s` of length `n`
  in the basis `Module.finBasis ℝ W`, positive torus points `t` all of whose root coordinates are
  at least `-θ`, and `ϖ ∈ Ω`. It is `constantTerm_chamber_bound` for `wordFamily` on
  `S ×ˢ Sw`, `Sw` the words of length `n`, with the growth hypotheses from
  `family_growth_bounds` and the torus shift equations from `hasTorusShiftEquations_of_le`.

The decay at the Siegel points. Let `j : T₀ → T` be a homomorphism of split tori such that the
positive points of `T₀` map to norm-one points of `G(𝔸)`; write `b` for the image in `G(𝔸)` of
a positive point of `T₀` (`positiveMap`).

- `step_decay_bound`: for a standard index `J`, a simple root `α`, a threshold `t`, a compact
  `Ω` and `k : ℕ` there is `B ≥ 0` with
  `‖(C_J f_x − C_{J ∖ α} f_x)(b ϖ)‖ ≤ B δ(b)^{1/2} (1 + R')^{2m} e^{−k s}` for `x ∈ S`, `b` in the
  weak chamber of threshold `t`, `ϖ ∈ Ω`, and all `R'`, `s` with `|log |β(b)|| ≤ R'` for every
  simple root `β` and `s ≤ log |α(b)|`. Here `δ = siegelModulus`.
- `sub_constantTerm_bound`: for a standard index `J` the same bound holds for `f_x − C_J f_x`
  when `s ≤ log |α(b)|` for every simple root `α ∉ J`.

Assembly:

- `subgroupConstantTerm_eq_of_eq`: constant terms along equal closed subgroups agree.
- `subgroupConstantTerm_central_mul`: if `z` commutes with every point and `f(z y) = c f(y)` for
  all `y`, then `CT f (z g) = c · CT f (g)` along every closed subgroup.
- `constantTerm_eq_of_subsingleton`: if `G(𝔸)` has one point, every constant term along a
  standard parabolic is the function itself (the normalized quotient measure is a probability
  measure).
- `complexParameterPairing_imaginaryParameter`, `norm_parameterPower_imaginaryParameter`:
  `⟨i x, y⟩ = i ⟨x, y⟩`, so `|m^{i x}| = 1`.

## The proof of `derivative_chamber_bound`, `step_decay_bound` and `sub_constantTerm_bound`

Fix the family `f`, a torus frame `Fr` of the standard parabolic family (coordinates
`crd t = ((crd t)_α)_{α ∈ Δ}` together with central coordinates, with
`log |α(t)| = step(α) · (crd t)_α`) and the order `m` of the shift equations.

*`derivative_chamber_bound`.* `family_regularity` gives slice smoothness of the constant terms
and `C_Q (D_s f x) = D_s (C_Q f x)`. Hence the constant terms of the members `u_s · f x` of
`wordFamily` are the derivative words `D_s (C_Q f x)`, which satisfy subunitary shift equations of
order `m` (`hasSubunitaryShiftEquations_adelicIteratedDirectionalValue`), hence torus shift
equations of order `m` along every `J ⊇ J'` (`hasTorusShiftEquations_of_le`, with the proved
`halfModulusRootProduct`). `isUniformGrowthFamily_wordFamily` and `family_growth_bounds` give the
growth hypotheses, and `constantTerm_chamber_bound` gives the bound for `C_J (u_s · f x)`, which is
`D_s (C_J f x)`.

*`step_decay_bound`.* Put `n₀ = k [F:ℚ]` and `Y_f` the image of `Ω` in `G(𝔸_f)`.
`exists_constantTermStep_decay` (with the given `j`, the threshold `t` and order `n₀`) gives a
compact `K' ⊇ Ω` and `C_dec ≥ 0`. Let `σ = ∑_{β ∈ Δ} step(β)^{-1}` and `θ = |log t| σ`;
`derivative_chamber_bound` for `J` and for `J ∖ α` (order `n₀`, compact `K'`, this `θ`) gives
`C₁` and `C₂`. The constant is `B = C_dec (C₁ + C₂) (2mσ + 3)^{2m}`. Given `b`, let `u` be the
image of `b` in `T`, so that `b = torusPoint u` in `G(𝔸)` and the roots take the same values at `u`
and `b`.

- The central coordinates of `u` vanish, because `b` is a norm-one point
  (`characterLog_eq_zero_iff`, `characterLog_map` and the defining property of the frame).
- The root coordinates are `(crd u)_β = log |β(b)| / step(β)`. On the weak chamber they are at
  least `-θ`; if `|log |β(b)|| ≤ R'` for all simple `β`, they are at most `R' σ` in absolute value,
  so `‖crd u‖ ≤ R' σ` (`TorusFrame.norm_crd_le`; `R' ≥ 0` because `α` is simple) and
  `2m ‖crd u‖ + 3 ≤ (2mσ + 3)(1 + R')`.
- `torusModulus u = siegelModulus b`, both being the product over the positive roots.
- For `k' ∈ K'` and a word `s` of length `n₀`, `D_s` of the step at `b k'` is
  `D_s (C_J f_x)(b k') − D_s (C_{J ∖ α} f_x)(b k')` (`adelicIteratedDirectionalValue_sub`), bounded
  by `M = (C₁ + C₂)(2m ‖crd u‖ + 3)^{2m} δ(b)^{1/2}`.
- The finite part of `b ϖ` is that of `ϖ` (`finite_positiveMap`), so it lies in `Y_f`.
  `exists_constantTermStep_decay` gives `‖step(b ϖ)‖ ≤ C_dec ρ^{n₀} M`, with
  `ρ = relativeCharacterDecay j α b = |α(b)|^{-1/[F:ℚ]}`. Then
  `ρ^{n₀} = e^{−k log |α(b)|} ≤ e^{−k s}`, and the two inequalities above give the bound.

*`sub_constantTerm_bound`.* By induction on the number `n` of simple roots outside a standard
index `J' ⊇ J`, there is `B ≥ 0` bounding `‖(f_x − C_{J'} f_x)(b ϖ)‖` as in the statement (the
hypothesis on `s` concerns the roots outside `J`). If `n = 0` then `J' = Δ` and `C_Δ f_x = f_x`
(`constantTerm_top`), so `B = 0`. Otherwise choose a simple root `α ∉ J'` and put
`J⁺ = J' ∪ {α}`. Then `J⁺ ∖ α = J'` (`removeSimpleRoot`), so
`f_x − C_{J'} f_x = (f_x − C_{J⁺} f_x) + (C_{J⁺} f_x − C_{J⁺ ∖ α} f_x)`. The first term is bounded
by the induction hypothesis for `J⁺`, the second by `step_decay_bound` for `J⁺` and `α`, since
`α ∉ J` gives `s ≤ log |α(b)|`. The constant is the sum of the two constants.

## The proof of `eisensteinConstantTermDecayReduction`

Fix the data of `EisensteinConstantTermDecayStatement`.

1. `EisensteinUnitaryUniformGrowthStatement` gives an open level `L`, an exponent `R` and smooth
   left `G(F)`-invariant functions `f x` with underlying function `E(i e(x))` for `x ∈ C`, with
   uniform moderate growth on `C`. `EisensteinUnitaryExponentStatement` gives `m` such that for
   every standard parabolic family, standard index and `x ∈ C` the constant term of `E(i e(x))`
   satisfies subunitary shift equations of order `m`. The witness is `2m`; it is chosen before
   the threshold `t`, the compact `Ω` and `k`.
2. From the Siegel setup: `i` is a maximal split torus, `ν` is generic, and `T₀` is a maximal split
   torus of the derived group, so `T₀` is split. `𝓕 = StandardParabolicFamily.ofMaximalSplitTorus`
   is the standard parabolic family of `(T, i, ν)`. For the index `J`, the radical of `𝓕` is
   `Standard.unipotentToParabolic i ν J ≫ Standard.parabolicHom i ν J =
   Standard.unipotentHom i ν J` (`Standard.unipotentToParabolic_comp`), so the constant term of the
   statement is `𝓕.constantTerm ⟨J, _⟩` (`subgroupConstantTerm_eq_of_eq`).
3. **The split component.** Let `z ∈ A_G`. By `canonicalSubgroup_eq_imageSubgroup`, `z` is the
   image of a positive point `z'` of the canonical split component `canonicalComponent F G`. This
   component is central, and it factors through the Levi of `P` as `j₀ ≫ l ≫ p`
   (`ParabolicRootPresentation.intermediateCentralFactor`). Since `φ` is `A_M`-equivariant (part
   of `IsSquareIntegrableInducedForm`) and `i e(x) ∈ D`, `eisensteinContinuation_splitCentre_mul`
   gives `E(i e(x))(z g) = c E(i e(x))(g)` for all `g`, where `c` is the value at `z'` of the
   restriction of `i e(x)` along `j₀ ≫ l`. By `parameterPower_parameterRestrict`, `c` is the value
   of `parameterPower F P (i e(x))` at the image of `z'` in `P(𝔸)`, so `|c| = 1`
   (`norm_parameterPower_imaginaryParameter`). As `z` is central
   (`positivePointMap_commute`), `subgroupConstantTerm_central_mul` gives the same factor for the
   constant term. Hence `‖(E − E_Q)(z b ω)‖ = ‖(E − E_Q)(b ω)‖`.
4. **Size zero.** If `N = 0`, `rho` is a closed embedding into the trivial group `GL_0(𝔸)`, so
   `G(𝔸)` has one point (`RepresentationGrowth.isClosedEmbedding_adelicMatrix`). Then
   `E_Q = E` (`constantTerm_eq_of_subsingleton`), and `B = 0` works.
5. **Positive size.** If `N > 0`, choose a torus frame of `𝓕` (`TorusFrame.nonempty`). The shift
   equations of step 1 are rewritten for the functions `f x`. The positive points of `T₀` map to
   norm-one points (`IsSiegelAlgebraicSetup.positiveNormOneMap`). `sub_constantTerm_bound` for
   `𝓕`, `j`, the index `⟨J, _⟩`, `t`, `Ω` and `k` gives `B`. After step 3, writing
   `z b ω = z (b ω)`, and replacing `E(i e(x))` by the function of `f x`, its bound is the
   conclusion.

## Scope

The module proves the implication only. It does not prove uniform moderate growth, the
subunitary exponents, Delorme's Lemma 3.1 for general smooth functions, or Proposition 4.1. The
derivative bounds of `derivative_chamber_bound` are stated for derivative words of a fixed length
on the chambers `{t : all root coordinates ≥ −θ}` of the maximal split torus; the conclusion
of the main theorem bounds only `E − E_Q` itself, as the statement requires.
