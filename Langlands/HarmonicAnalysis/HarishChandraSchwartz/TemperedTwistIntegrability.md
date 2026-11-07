# Tempered representations and the hypotheses of Waldspurger, Proposition III.7.1

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedTwistIntegrability`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitPolynomialOperator` (Worker 249):
  `orbitPolynomialOperator`, `orbitPolynomialOperator_eq_smul_of_equiv`,
  `orbitPolynomialOperator_eq_zero`, `existsUnique_orbitIsotypic_decomposition`,
  `hasTemperedCoefficients_of_injective`, `hasTemperedCoefficients_of_surjective`; through it
  `TraceFamilyScalar` (`map_mk_restrict_preimage`, `measurable_quotientMk`,
  `contragredientRep`), `SchurOrthogonality` (`orthogonalityIntegrand`,
  `orthogonalityIntegrand_mk`, `norm_character_eq_one`), `SchwartzAction`
  (`HasTemperedCoefficients`, `continuous_coefficient`, `ext_smoothDual`), `CoefficientCutoff`
  (`HasRapidlyDecreasingCoefficientsOn`), `L2` (`L2Weights`), `Translations`
  (`TranslationWeights`), `Langlands.Representation.Twist.SmoothPartDefinitions`
  (`smoothContragredientTwistEquiv`), `Langlands.Representation.Twist.SmoothProof`
  (`isSmooth_twist_iff`), `Langlands.Representation.Smooth.Contragredient.Definitions`
  (`smoothBidual`, `smoothContragredient`), `Langlands.Representation.Smooth.Admissibility.EmbeddingProof`
  (`isAdmissible_of_injective`) and `Langlands.Representation.Unramified.SphericalConstituentExistenceProof`
  (`SphericalExistence.isAdmissible_of_surjective`);
- `Langlands.Representation.Smooth.Schur.Proof` (`admissibleSchur_centralCharacter`: the center
  acts on an irreducible admissible representation through a character);
- from Mathlib `tendsto_pow_const_div_const_pow_of_one_lt`, `pow_card_eq_one'`,
  `pow_eq_one_iff_of_nonneg`, `integrableOn_finite_iUnion`, `integrable_map_measure`,
  `MeasurePreserving.integrableOn_comp_preimage`, `measurePreserving_mul_left`,
  `QuotientGroup.isQuotientMap_mk`, `Subgroup.isOpen_mono` and `setLIntegral_le_lintegral`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quoted lines carry no overline (checked on the rendered PDF pages 31 and 41).

- III.1, printed p. 265 (PDF p. 31), on the integral `I(v₁, v̌₁, v₂, v̌₂)` over `A_G \ G` of the
  product of a coefficient of `π₁` and one of `π₂`: "Cette intégrale est convergente d'après
  III.1.2 et II.1.5."
- III.2, printed p. 265: "Notons `C^w_lisse(G)` le sous-espace des `f ∈ C_lisse(G)` pour
  lesquelles il existe `c > 0` et `r ∈ ℝ` tels que pour tout `g ∈ G`,
  `|f(g)| ⩽ c Ξ(g)(1 + σ(g))^r`. [...] On dit que `π` est tempérée si `A(π) ⊂ A^w(G)`."
- Proof of Proposition III.7.1, printed p. 275 (PDF p. 41): "D'après III.1 (2), qui se
  généralise au cas où `π₂` est seulement tempérée, cette intégrale est nulle si
  `π ≄ ω ⊗ χ`." and "Comme `π` est tempérée, `S(π) ⊂ Im X(G)`."

The module proves these two consequences of temperedness in the abstract setting of the
Library's `TraceFamilyScalar`, and derives Proposition III.7.1 (ii), (iii) and Corollary III.7.2
for tempered representations from the Library's `OrbitPolynomialOperator`.

## Correspondence and generalizations

- Setting. As in `TraceFamilyScalar` and `OrbitPolynomialOperator`: a surjective `p : G →* Λ`
  onto a commutative group with open kernel in place of `G → G / G¹`, a central subgroup `A` in
  place of `A_G` with `Λ / p(A)` finite, the measure compatibility `hcompat` with constant `m`,
  weights `Ξ`, `σ`. "Tempered" is `HasTemperedCoefficients Ξ σ π` (the source's definition, with
  the coefficients of smooth functionals).
- The convergence of the source ("d'après III.1.2 et II.1.5") is
  `integrable_orthogonalityIntegrand_of_tempered`: Corollary III.1.2 (for `ω` square
  integrable, `|f(g)| ⩽ c Ξ(g)(1 + σ(g))^{-r}` on `G¹` for every coefficient `f` and every `r`)
  enters as the hypothesis `hD` (rapid decay on `ker p` of the coefficients of the contragredient
  of `ω`, as in `TraceFamilyScalar`), Lemma II.1.5 as
  `L2Weights μ Ξ σ` (`∫_G Ξ² (1 + σ)^{-d} < ∞`), and Lemma II.1.2 as `TranslationWeights Ξ σ`.
  The tempered representation may be twisted by a unitary character `χ'` with open kernel.
- `S(π) ⊂ Im X(G)` corresponds to `norm_centralCharacter_eq_one`: the character by which `A`
  acts on a nonzero representation with tempered coefficients is unitary. The proof uses that
  `Ξ` is positive and invariant under `A` (`hΞA`) and that `σ` is nonnegative and subadditive
  (`hσ`); these are explicit hypotheses on the abstract weights.
- The Library's hypothesis `hint` quantifies over all characters `χ'` of `G` such that
  `π ⊗ χ'` acts on `A` through `cω`. A nonzero smooth functional on `π ⊗ χ'` forces `χ'` to
  have open kernel (`isOpen_ker_of_smoothDual_ne_zero`), and `|χ'| = 1` on `A` follows from the
  unitarity of `cπ` and `cω`. To conclude that `χ'` is unitary, `hint_of_tempered` assumes
  `IsUnitaryDetecting A` (every character of `G` with open kernel and absolute value `1` on `A`
  is unitary). By `isUnitaryDetecting_of_norm_eq_one_on_ker`, it holds when every character of
  `G` with open kernel has absolute value `1` on `ker p`. In the source the relevant characters
  are the unramified characters of `X(G)`, which are trivial on `G¹`. This hypothesis is not
  derived here.
- Derived results, not statements of the paper: `le_one_of_pow_le`,
  `le_add_nsmul_of_subadditive`, `exists_centralCharacter_of_isIrreducible`,
  `isUnitaryDetecting_of_norm_eq_one_on_ker`, `isOpen_ker_of_smoothDual_ne_zero`,
  `integrable_of_integrableOn_preimage`, `hsub_of_tempered` and the definition
  `IsUnitaryDetecting`.

## Scope and hypotheses

- `le_one_of_pow_le`: real `x`, `D`, `k : ℕ` and `h : ∀ n, xⁿ ≤ D (1 + n)^k`.
- Section `Character`: `G` a topological group, `V : Type v`, `ρ : Representation ℂ G V`, a
  subgroup `A`; `exists_centralCharacter_of_isIrreducible` takes `hA : A ≤ center G`,
  `IsAdmissible ρ` and `ρ.IsIrreducible`; `le_add_nsmul_of_subadditive` takes a subadditive
  `σ` on a group; `norm_centralCharacter_eq_one` takes `[Nonempty (CompactOpenSubgroup G)]`,
  `[Nontrivial V]`, `IsSmooth ρ`, `HasTemperedCoefficients Ξ σ ρ`, a character `c : A →* ℂˣ`
  with `hc : ∀ a x, ρ a x = c a • x`, `hΞ0 : ∀ g, 0 < Ξ g`, `hΞ : ∀ a ∈ A, ∀ g,
  Ξ (a * g) = Ξ g`, `hσ0 : ∀ g, 0 ≤ σ g`, `hσ : ∀ g h, σ (g * h) ≤ σ g + σ h`.
- Section `Twist`: `IsUnitaryDetecting A` for a subgroup of a topological group;
  `isUnitaryDetecting_of_norm_eq_one_on_ker` for a group with a topology, `p : G →* Λ` with
  `[Finite (Λ ⧸ A.map p)]` and `hker : ∀ θ, IsOpen θ.ker → ∀ k ∈ ker p, ‖θ k‖ = 1`;
  `isOpen_ker_of_smoothDual_ne_zero` takes `IsSmooth ρ`, `χ' : G →* ℂˣ` and a nonzero
  `ℓ : SmoothDual (twist χ' ρ)`.
- Section `Integrability`: `G` a topological group with `[MeasurableSpace G] [BorelSpace G]`,
  `μ` left invariant, `p : G →* Λ`, a normal subgroup `A`, `[MeasurableSpace (G ⧸ A)]
  [BorelSpace (G ⧸ A)]`, `ν` left invariant, `m : ℝ≥0∞`.
  `integrable_of_integrableOn_preimage` takes `[Finite (Λ ⧸ A.map p)]`, `hp` (surjective),
  `hcompat`, `hm0 : m ≠ 0`, `hm : m ≠ ∞`, a continuous `H : G ⧸ A → ℂ` and the integrability of
  `H ∘ mk` on every fibre `p⁻¹(p g)`. `integrable_orthogonalityIntegrand_of_tempered` takes, for
  `ω` with `hω : ∀ a x, ω a x = cω a • x`: `[Finite (Λ ⧸ A.map p)]`, `hp`, `hcompat`, `hm0`,
  `hm`, `hN : IsOpen (ker p)`, `ht : TranslationWeights Ξ σ`, `hw : L2Weights μ Ξ σ`,
  `IsSmooth ω`, `hD`, `IsSmooth π`, `HasTemperedCoefficients Ξ σ π`, `χ'` with open kernel
  (`hχo`) and `‖χ' g‖ = 1` (`hχu`), and `hχ' : ∀ a x, twist χ' π a x = cω a • x`.
  `hint_of_tempered` takes the same hypotheses except `χ'`, `hχo`, `hχu`, `hχ'`, together with
  `hωu : ∀ a, ‖cω a‖ = 1`, `hunit : IsUnitaryDetecting A`, `cπ : A →* ℂˣ` with
  `hπc : ∀ a x, π a x = cπ a • x` and `hπu : ∀ a, ‖cπ a‖ = 1`.
- Section `Corollaries`: the variables of `OrbitPolynomialOperator`'s section `Decomposition`
  (`G` with `[Nonempty (CompactOpenSubgroup G)]`, second countable, `μ` Haar, s-finite and right
  invariant, `K` compact, `A` normal and central (`hA`), `ν` Haar and invariant under inversion,
  `hcof`, `ω` with `hω`, `hsq`, `hiω`, `[Fintype (Λ ⧸ A.map p)]`, `V : Type w`).
  `hsub_of_tempered` takes `hp`, `hN`, `hm`, `hm0`, `hcompat`, `ht`, `hw`, `hD`, `hΞA`, `hσ`,
  `hunit` and an admissible `π` with tempered coefficients;
  `existsUnique_orbitIsotypic_decomposition_of_tempered` takes the hypotheses of
  `existsUnique_orbitIsotypic_decomposition` with `hΞA`, `hσ`, `hunit` in place of `hsub`;
  `orbitPolynomialOperator_eq_smul_of_equiv_of_tempered` takes those of
  `orbitPolynomialOperator_eq_smul_of_equiv` with `hunit` in place of `hint`;
  `orbitPolynomialOperator_eq_zero_of_tempered` takes those of `orbitPolynomialOperator_eq_zero`
  with `hm0`, `hΞA`, `hσ`, `hunit` in place of `cπ`, `hπc`, `hπu`, `hint`.

## Definitions

- `IsUnitaryDetecting A`: every `θ : G →* ℂˣ` with open kernel and `‖θ a‖ = 1` for all `a ∈ A`
  satisfies `‖θ g‖ = 1` for all `g`.

## Results

- `le_one_of_pow_le`: if `xⁿ ≤ D (1 + n)^k` for all `n`, then `x ≤ 1`.
- `exists_centralCharacter_of_isIrreducible`: a character `c` of `A` with `ρ(a) = c(a)`.
- `le_add_nsmul_of_subadditive`: `σ(gⁿ) ≤ σ(1) + n σ(g)`.
- `norm_centralCharacter_eq_one` (**`S(π) ⊂ Im X(G)` in the proof of Proposition III.7.1**):
  `‖c a‖ = 1` for all `a ∈ A`.
- `isUnitaryDetecting_of_norm_eq_one_on_ker`: the sufficient condition above.
- `isOpen_ker_of_smoothDual_ne_zero`: `χ'` has open kernel.
- `integrable_of_integrableOn_preimage`: `H` is integrable on `G / A`.
- `integrable_orthogonalityIntegrand_of_tempered` (**the convergence of III.1, for a tempered
  representation**): `orthogonalityIntegrand A hχ' hω v₁ ℓ₁ v₂ ℓ₂`, the function
  `gA ↦ ℓ₁((π ⊗ χ')(g) v₁) ℓ₂(ω(g⁻¹) v₂)`, is integrable on `G / A` for all smooth `ℓ₁`, `ℓ₂`.
- `hint_of_tempered`: the hypothesis `hint` of `TraceFamilyScalar` for `π`.
- `hsub_of_tempered`: the hypothesis `hsub` of `OrbitPolynomialOperator` for `π`.
- `existsUnique_orbitIsotypic_decomposition_of_tempered` (**Corollary III.7.2 for tempered
  representations**): the unique decomposition `V = V₁ ⊕ V₂` with (i) and (ii).
- `orbitPolynomialOperator_eq_smul_of_equiv_of_tempered` (**Proposition III.7.1 (iii)**):
  `π(p) = b̂(χ₁) • id` if `π ≃ ω ⊗ (χ₁ ∘ p)`, `χ₁` unitary.
- `orbitPolynomialOperator_eq_zero_of_tempered` (**Proposition III.7.1 (ii)**): `π(p) = 0` for
  `π` irreducible, tempered and not equivalent to any `ω ⊗ (χ ∘ p)`, `χ` unitary.

## Proof notes

1. `le_one_of_pow_le`: if `x > 1`, then `nᵏ / xⁿ → 0`
   (`tendsto_pow_const_div_const_pow_of_one_lt`), while `xⁿ ≤ D 2ᵏ nᵏ` for `n ≥ 1`.
2. `exists_centralCharacter_of_isIrreducible`: compose the central character of
   `admissibleSchur_centralCharacter` with the inclusion `A → center G`.
3. `norm_centralCharacter_eq_one`: choose `v ≠ 0` and a smooth `ℓ` with `ℓ(v) ≠ 0`
   (`ext_smoothDual`). For `b ∈ A`, `ℓ(ρ(bⁿ) v) = c(b)ⁿ ℓ(v)`, `Ξ(bⁿ) = Ξ(1)` and
   `1 + σ(bⁿ) ≤ (1 + σ(1) + σ(b)) (1 + n)`; the tempered bound gives
   `‖c(b)‖ⁿ ≤ D (1 + n)^⌈|r|⌉` and step 1 gives `‖c(b)‖ ≤ 1`. Applied to `b = a` and `a⁻¹`.
4. `isUnitaryDetecting_of_norm_eq_one_on_ker`: with `n = |Λ / p(A)|`, `p(g)ⁿ = p(a)` for some
   `a ∈ A`, so `a⁻¹ gⁿ ∈ ker p` and `‖θ(g)‖ⁿ = ‖θ(a)‖ ‖θ(a⁻¹ gⁿ)‖ = 1`.
5. `isOpen_ker_of_smoothDual_ne_zero`: take `v` with `ℓ(v) ≠ 0`, `K₁` fixing `v` and `K₂` fixing
   `ℓ`. For `k ∈ K₁ ∩ K₂`, `ℓ(v) = ℓ((π ⊗ χ')(k⁻¹) v) = χ'(k)⁻¹ ℓ(v)`, so `K₁ ∩ K₂ ⊂ ker χ'`.
6. `integrable_of_integrableOn_preimage`: choose `g_q` with `p(g_q)` in each class `q` of
   `Λ / p(A)`; the images `T_q` of the fibres `p⁻¹(p(g_q))` cover `G / A`. On `T_q`,
   `ν|_{T_q} = m⁻¹ mk_*(μ|_{p⁻¹(p(g_q))})` (`map_mk_restrict_preimage`), so `H` is integrable on
   `T_q` (`integrable_map_measure`); conclude with `integrableOn_finite_iUnion`.
7. `integrable_orthogonalityIntegrand_of_tempered`: the integrand `H` is continuous on `G / A`
   (coefficients of the smooth `π ⊗ χ'` and `ω`, `QuotientGroup.isQuotientMap_mk`). By step 6 it
   suffices that `k ↦ H(g k)` is integrable on `ker p` (left translation by `g`,
   `MeasurePreserving.integrableOn_comp_preimage`). For `k ∈ ker p`:
   `|ℓ₁((π ⊗ χ')(g k) v₁)| = |ℓ₁(π(g k) v₁)| ≤ |C₁| Ξ(g k) (1 + σ(g k))^{|r₁|}` (tempered
   growth, with `ℓ₁` viewed in `SmoothDual π` through `smoothContragredientTwistEquiv`),
   `Ξ(g k) ≤ |C_t| Ξ(k) (1 + σ(k))^{d_t}` and `1 + σ(g k) ≤ |C_h| (1 + σ(k))`
   (`TranslationWeights`), and `ℓ₂(ω((g k)⁻¹) v₂) = ℓ₂(ω(k⁻¹) ω(g⁻¹) v₂)` is the coefficient of
   the contragredient of `ω` at `k` against the evaluation at `ω(g⁻¹) v₂` (`smoothBidual`),
   bounded by `|C₂| Ξ(k) (1 + σ(k))^{-r₂}` with `r₂ = |r₁| + d_t + d` (`hD`). The product is at
   most `K₀ Ξ(k)² (1 + σ(k))^{-d}`, whose integral over `G` is finite (`L2Weights.square`).
8. `hint_of_tempered`: if `ℓ₁ = 0` the integrand is `0`. Otherwise `χ'` has open kernel
   (step 5); evaluating `hχ'` on a nonzero vector gives `χ'(a) cπ(a) = cω(a)`, so `‖χ'(a)‖ = 1`
   on `A`, and `hunit` makes `χ'` unitary; apply step 7.
9. `hsub_of_tempered`: an irreducible subquotient `π'` of `π` is admissible with tempered
   coefficients (`isAdmissible_of_injective`, `isAdmissible_of_surjective`,
   `hasTemperedCoefficients_of_injective`, `hasTemperedCoefficients_of_surjective`); step 2
   gives its character, step 3 its unitarity (`ht.pos`, `ht.nonneg`), step 8 the integrability
   (with `cω` unitary by `norm_character_eq_one` and `ω` smooth by `hsq`).
10. The corollaries apply `existsUnique_orbitIsotypic_decomposition` with step 9,
    `orbitPolynomialOperator_eq_smul_of_equiv` with step 8 (the character of `A` on `π` read off
    from `e` as `(χ₁ ∘ p) cω`, unitary), and `orbitPolynomialOperator_eq_zero` with steps 2, 3
    and 8.
