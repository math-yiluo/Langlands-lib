# Schur orthogonality and the formal degree (Waldspurger III.1 (2), (3))

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchurOrthogonality`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.Representation.Plancherel.CentralSubgroupCoefficients`
(`IsSquareIntegrableModCentralSubgroup`, `centralSubgroupCoefficientNorm`,
`centralSubgroupCoefficientNorm_mk`), `Langlands.Representation.Smooth.Contragredient.WeakIntertwiner`
(`exists_intertwiningMap_of_weakForm_of_compact_cofinal`) and, through it, the smooth dual
(`SmoothDual`, `smoothDualPairing`, `smoothContragredient`);
`Langlands.Representation.Smooth.Schur.Proof` (`admissibleSchur_scalarEndomorphism`);
`Langlands.Representation.MatrixCoefficient.LawsProof` (`matrixCoefficient_isLocallyConstant`);
`Langlands.Representation.Unitary.Basic` (`InvariantPositiveForm`, `IsUnitarizable`);
`Langlands.Representation.Unitary.SquareIntegrableProof`
(`exists_smoothDual_apply_ne_zero_of_compact_cofinal`, `eq_zero_of_matrixCoefficient_vanishes`);
and from Mathlib `Mathlib.RepresentationTheory.Irreducible` (`Representation.IsIrreducible`,
the instance `Subsingleton (IntertwiningMap ρ σ)` for irreducible `ρ`, `σ` with
`IsEmpty (Equiv ρ σ)`), `Mathlib.MeasureTheory.Group.Integral`
(`integral_inv_eq_self`, `integral_mul_left_eq_self`) and
`Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap` (`integral_conj`,
`integral_complex_ofReal`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.
Printed page numbers; the PDF page is the printed page minus 234.

- III.1, printed p. 263 (PDF p. 29): "Soit `(π, V)` une représentation admissible de `G`
  admettant un caractère central unitaire. On dit que `π` est de carré intégrable si tous les
  coefficients de `π` sont de carré intégrable sur `A_G \ G`."
- Lemme III.1.3, printed p. 264 (PDF p. 30): "Toute représentation admissible de carré
  intégrable de `G` est unitaire et semi-simple." The proof takes a finitely generated
  subrepresentation `V'` with generators `v_1, …, v_n` and the form
  `(v̌_1, v̌_2) ↦ Σ_i ∫_{A_G \ G} conj(⟨π(g) v_i, v̌_1⟩) ⟨π(g) v_i, v̌_2⟩ dg` on `V̌'` (the bar
  is over the first coefficient: the form is conjugate linear in `v̌_1`), which is
  positive definite and `G`-invariant.
- III.1, printed p. 265 (PDF p. 31): "Soient `(π_1, V_1)` et `(π_2, V_2)` deux
  représentations irréductibles de carré intégrable de `G`. Supposons que les restrictions à
  `A_G` de leurs caractères centraux coïncident. Pour `v_1 ∈ V_1`, `v̌_1 ∈ V̌_1`, `v_2 ∈ V_2`,
  `v̌_2 ∈ V̌_2`, posons
  `I(v_1, v̌_1, v_2, v̌_2) = ∫_{A_G \ G} ⟨π_1(g) v_1, v̌_1⟩ ⟨v_2, π̌_2(g) v̌_2⟩ dg`.
  Cette intégrale est convergente d'après III.1.2 et II.1.5. On montre :
  (2) si `π_1 ≄ π_2`, `I(v_1, v̌_1, v_2, v̌_2) = 0` pour tous `v_1, v̌_1, v_2, v̌_2` ;
  (3) si `(π_1, V_1) = (π_2, V_2)`, il existe un réel `d(π_1) > 0` tel que
  `I(v_1, v̌_1, v_2, v̌_2) = d(π_1)^{-1} ⟨v_1, v̌_2⟩ ⟨v_2, v̌_1⟩` pour tous
  `v_1, v̌_1, v_2, v̌_2`. Cf. [C, Proposition 5.2.4]. Le réel `d(π_1)` est appelé le degré
  formel de `π_1`."
- Proof of Proposition III.7.1, printed p. 275 (PDF p. 41): "D'après III.1 (2), qui se
  généralise au cas où `π_2` est seulement tempérée, cette intégrale est nulle si
  `π ≄ ω ⊗ χ`." This module states (2) both for square integrable `π_1`, `π_2` and, more
  generally, for irreducible admissible `π_1`, `π_2` for which all the integrands are
  integrable; for tempered `π_2` that integrability is not proved here.

Waldspurger does not prove (2) and (3); he cites Casselman [C, Prop. 5.2.4]. The proofs here
are written for this module (see Proof notes). The Lean statements follow the source with these
translations:

- `⟨v_2, π̌_2(g) v̌_2⟩ = (π̌_2(g) v̌_2)(v_2) = v̌_2(π_2(g^{-1}) v_2)`. The integrand is
  therefore `g ↦ ℓ₁(π₁(g) v₁) ℓ₂(π₂(g⁻¹) v₂)`, where `ℓ₁ = v̌_1` and `ℓ₂ = v̌_2` are smooth
  functionals (elements of `SmoothDual`).
- `A_G \ G` is the quotient `G ⧸ A` by an arbitrary normal subgroup `A ≤ Subgroup.center G`.
  Since `A` is central, left and right cosets agree. That `A` is Waldspurger's split
  component `A_G` is not asserted.
- "de carré intégrable" is the Library's `IsSquareIntegrableModCentralSubgroup A hA π μ`:
  `π` is admissible, it has a unitary character of the full center
  (`UnitaryCentralCharacter π`), and for every smooth functional `ℓ` and vector `v` the
  function `gA ↦ ‖ℓ(π(g) v)‖` on `G ⧸ A` lies in `L²(μ)`. Its admissibility is the Library's
  `IsAdmissible` (smooth, finite-dimensional `V^K` for every open subgroup `K`).
- "irréductible" is Mathlib's `Representation.IsIrreducible` (algebraic irreducibility).
  "`π_1 ≄ π_2`" is `IsEmpty (π₁.Equiv π₂)`: there is no `G`-equivariant linear isomorphism.
  "`(π_1, V_1) = (π_2, V_2)`" is the case of one representation `π`.
- "les restrictions à `A_G` de leurs caractères centraux coïncident" is a single character
  `χ : A →* ℂˣ` with `π₁(a) x = χ(a) x` and `π₂(a) x = χ(a) x` for all `a ∈ A` (hypotheses
  `h₁`, `h₂`).

## Scope: abstract data and explicit hypotheses

`G` is a topological group (`[IsTopologicalGroup G]`); the quotient `G ⧸ A` carries the quotient
topology and a Borel measurable structure (`[BorelSpace (G ⧸ A)]`). The representations are
`Representation ℂ G V` on complex vector spaces without topology. Two hypotheses are not proved
here for Waldspurger's group and are explicit:

- `μ` is a Haar measure on the group `G ⧸ A` that is invariant under inversion
  (`[μ.IsHaarMeasure] [μ.IsInvInvariant]`), i.e. `G ⧸ A` is unimodular and `μ` is its Haar
  measure. Waldspurger's `G` is unimodular; that `G / A_G` is then unimodular is not proved
  here.
- `hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K`: every
  open subgroup contains a compact open subgroup. For a `p`-adic group this holds because the
  compact open subgroups form a neighbourhood basis of `1`; this is not proved here.

The hypotheses of each result are:

- `integral_mul_right_eq_self_of_inv`: a group `Q` with `[MeasurableMul Q] [MeasurableInv Q]`
  and a measure with `[μ.IsMulLeftInvariant] [μ.IsInvInvariant]`.
- `orthogonalityFun_mul` and the definition `orthogonalityIntegrand`: `h₁`, `h₂` only (no
  topology, no normality of `A`).
- `orthogonalityIntegrand_mk`, `orthogonalityIntegrand_add_left`, `_smul_left`, `_add_right`,
  `_smul_right`, `_add_left_dual`, `_smul_left_dual`, `_add_right_vec`, `_smul_right_vec`:
  `h₁`, `h₂`.
- `continuous_orthogonalityIntegrand`: `[IsTopologicalGroup G]`, `h₁`, `h₂`, and
  `hπ₁ : IsSmooth π₁`, `hπ₂ : IsSmooth π₂`.
- `integrable_orthogonalityIntegrand`: the section data (`A` normal and central, `μ` Haar and
  inversion invariant on `G ⧸ A`), `h₁`, `h₂`,
  `hsq₁ : IsSquareIntegrableModCentralSubgroup A hA π₁ μ` and `hsq₂` (the same for `π₂`).
- `orthogonalityIntegral_rho_left`: the section data and `h₁`, `h₂`.
  `orthogonalityIntegral_rho_right`: the same without inversion invariance of `μ`.
- `orthogonalityFormLeft`, `orthogonalityFormRight`: `h₁`, `h₂`, the measure `μ` and
  `hint : ∀ v₁ ℓ₁ v₂ ℓ₂, Integrable (orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val v₂ ℓ₂.val) μ`
  (no central or square integrability hypothesis).
- `exists_intertwiningMap_orthogonalityIntegral_left`, `_right`: the section data (`μ` Haar on
  `G ⧸ A`; inversion invariance only for `_left`), `h₁`, `h₂`, `hint`, `hcof`,
  `hπ₁ : IsAdmissible π₁` and `hπ₂ : IsAdmissible π₂`.
- `orthogonalityIntegral_eq_zero_of_integrable` (III.1 (2), integrable form): in addition
  `hi₁ : π₁.IsIrreducible`, `hi₂ : π₂.IsIrreducible` and `hne : IsEmpty (π₁.Equiv π₂)`.
- `orthogonalityIntegral_eq_zero` (III.1 (2)): the section data, `h₁`, `h₂`, `hcof`, `hsq₁`,
  `hsq₂`, `hi₁`, `hi₂` and `hne`.
- `formFun_mul` and the definition `formIntegrand`: one representation `π` with
  `h : ∀ a x, π a x = χ a • x` and `hu : ∀ a, ‖χ a‖ = 1` (`χ` unitary); also for
  `formIntegrand_mk`, `formIntegrand_swap`, `formIntegrand_self_mk`, `formIntegrand_self`,
  `formIntegrand_add_left`, `formIntegrand_smul_left`. `continuous_formIntegrand` adds
  `[IsTopologicalGroup G]` and `hπ : IsSmooth π`.
- `exists_smoothDual_eq_one`: `[IsTopologicalGroup G]`, `hcof`, `hπ : IsSmooth π`, `v ≠ 0`.
- `integrable_formIntegrand`, `invariantForm_add_left`, `invariantForm_self_re_pos`: `μ` Haar on
  `G ⧸ A` (inversion invariance not needed), `h`, `hu`,
  `hsq : IsSquareIntegrableModCentralSubgroup A hA π μ`; the last also `ℓ.val v ≠ 0`.
- The definition `invariantForm` and `invariantForm_smul_left`, `invariantForm_swap`,
  `invariantForm_self`: `h`, `hu` and the measure `μ` only.
- `invariantForm_rho`: `μ` Haar and inversion invariant, `h`, `hu`.
- `invariantForm_self_re_pos_of_ne_zero`: `μ` Haar and inversion invariant, `h`, `hu`, `hsq`,
  `hi`, `ℓ.val x₀ ≠ 0` and `v ≠ 0`.
- `norm_character_eq_one`: `μ` Haar on `G ⧸ A` (for `hsq`), `h`, `hsq` and `hi`.
- The definition `invariantPositiveForm` and `invariantPositiveForm_inner`: `μ` Haar and
  inversion invariant, `h`, `hu`, `hsq`, `hi` and `ℓ.val x₀ ≠ 0`.
- `isUnitarizable_of_isSquareIntegrable`: `μ` Haar and inversion invariant, `h`, `hcof`, `hsq`
  and `hi`.
- The definition `formFunctional` and `formFunctional_apply`: `μ` Haar and inversion
  invariant, `h`, `hu`, `hsq`.
- `exists_orthogonalityIntegral_eq_mul`, `exists_formalDegree` (III.1 (3)), the definition
  `formalDegree`, `formalDegree_pos`, `orthogonalityIntegral_eq_formalDegree`: `μ` Haar and
  inversion invariant on `G ⧸ A`, `h`, `hcof`, `hsq` and `hi`. The unitarity `hu` of `χ` is
  not a hypothesis there: it is derived from `hsq`.
- `formalDegree_unique`: `μ` Haar, `h`, `hcof`, `hsq`, `hi` and the two formulas for `d`, `d'`.

## Definitions

- `orthogonalityFun π₁ π₂ v₁ ℓ₁ v₂ ℓ₂ : G → ℂ`, `g ↦ ℓ₁(π₁(g) v₁) ℓ₂(π₂(g⁻¹) v₂)`, for algebraic
  functionals `ℓ₁ : Module.Dual ℂ V₁`, `ℓ₂ : Module.Dual ℂ V₂`.
- `orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ : G ⧸ A → ℂ`, the same function on `G ⧸ A`
  (`Quotient.lift`; well defined by `orthogonalityFun_mul`).
- `orthogonalityIntegral A μ h₁ h₂ v₁ ℓ₁ v₂ ℓ₂ : ℂ`, for smooth functionals
  `ℓ₁ : SmoothDual π₁`, `ℓ₂ : SmoothDual π₂`: Waldspurger's
  `I(v₁, ℓ₁, v₂, ℓ₂) = ∫_{G ⧸ A} ℓ₁(π₁(g) v₁) ℓ₂(π₂(g⁻¹) v₂) dμ`.
- `orthogonalityFormLeft … ℓ₁ v₂ : V₁ →ₗ[ℂ] SmoothDual π₂ →ₗ[ℂ] ℂ`, `(v₁, ℓ₂) ↦ I(v₁, ℓ₁, v₂, ℓ₂)`,
  and `orthogonalityFormRight … v₁ ℓ₂ : V₂ →ₗ[ℂ] SmoothDual π₁ →ₗ[ℂ] ℂ`,
  `(v₂, ℓ₁) ↦ I(v₁, ℓ₁, v₂, ℓ₂)` (helpers for the proof, bilinear by integrability).
- `formFun π ℓ v w : G → ℂ`, `g ↦ ℓ(π(g) v) conj(ℓ(π(g) w))`, and
  `formIntegrand A h hu ℓ v w : G ⧸ A → ℂ`, the same function on `G ⧸ A` (well defined because
  `|χ| = 1`).
- `invariantForm A μ h hu ℓ v w : ℂ`, for a smooth functional `ℓ`:
  `(v, w) = ∫_{G ⧸ A} ℓ(π(g) v) conj(ℓ(π(g) w)) dμ`. It is linear in `v` and conjugate linear
  in `w`. Waldspurger's form in the proof of Lemma III.1.3 is conjugate linear in its first
  argument and lives on `V̌'`, summing over generators of `V'`. The form here exchanges the
  roles of `V` and `V̌`, uses one functional `ℓ` in place of the sum over generators, and puts
  the bar on the second factor (derived variant, see Proof notes).
- `invariantPositiveForm A hA μ h hu hsq hi ℓ hx₀ : InvariantPositiveForm π`, the same form as
  a Library invariant positive definite Hermitian form. The Library form follows Mathlib's
  convention, conjugate linear in the first argument (as Waldspurger's form is), so the
  arguments are reversed: its `inner v w` is `(w, v) = ∫ conj(ℓ(π(g) v)) ℓ(π(g) w) dμ`
  (`invariantPositiveForm_inner`).
- `formFunctional A hA μ h hu hsq ℓ w : SmoothDual π`, the smooth functional `x ↦ (x, w)`.
- `formalDegree A hA μ h hcof hsq hi : ℝ`, the formal degree `d(π)` of III.1 (3) for the Haar
  measure `μ`, chosen by `Classical.choose` from `exists_formalDegree`; by
  `formalDegree_unique` it does not depend on a choice.

## Results

- `integral_mul_right_eq_self_of_inv`: `∫ F(q x) dμ(q) = ∫ F dμ` for `F : Q → ℂ`.
- `orthogonalityFun_mul`: `orthogonalityFun … (g a) = orthogonalityFun … g` for `a ∈ A`.
- `orthogonalityIntegrand_mk` (value at `gA`) and the eight linearity lemmas: the integrand is
  additive and homogeneous in each of `v₁`, `ℓ₁`, `v₂`, `ℓ₂`.
- `continuous_orthogonalityIntegrand`: the integrand is continuous on `G ⧸ A`.
- `integrable_orthogonalityIntegrand` (the convergence of `I` in III.1): the integrand is
  integrable on `G ⧸ A` for all `v₁, ℓ₁, v₂, ℓ₂`.
- `orthogonalityIntegral_rho_left`: `I(π₁(h) v₁, ℓ₁, v₂, ℓ₂) = I(v₁, ℓ₁, v₂, π̃₂(h⁻¹) ℓ₂)`;
  `orthogonalityIntegral_rho_right`: `I(v₁, ℓ₁, π₂(h) v₂, ℓ₂) = I(v₁, π̃₁(h⁻¹) ℓ₁, v₂, ℓ₂)`,
  where `π̃ = smoothContragredient π`.
- `exists_intertwiningMap_orthogonalityIntegral_left`: for fixed `ℓ₁`, `v₂` there is an
  intertwiner `T : π₁ → π₂` with `ℓ₂(T v₁) = I(v₁, ℓ₁, v₂, ℓ₂)` for all `v₁`, `ℓ₂`;
  `exists_intertwiningMap_orthogonalityIntegral_right`: for fixed `v₁`, `ℓ₂` there is
  `T : π₂ → π₁` with `ℓ₁(T v₂) = I(v₁, ℓ₁, v₂, ℓ₂)` for all `v₂`, `ℓ₁`.
- `orthogonalityIntegral_eq_zero_of_integrable`: if `π₁`, `π₂` are irreducible admissible, not
  equivalent, and all integrands are integrable, then `I(v₁, ℓ₁, v₂, ℓ₂) = 0` (the
  generalization used on p. 275).
- `orthogonalityIntegral_eq_zero` (**III.1 (2)**): if `π₁`, `π₂` are irreducible, square
  integrable modulo `A` and not equivalent, `I(v₁, ℓ₁, v₂, ℓ₂) = 0` for all
  `v₁, ℓ₁, v₂, ℓ₂` (the previous result with `hint` from `integrable_orthogonalityIntegrand`).
- `formFun_mul`, `formIntegrand_mk`, `formIntegrand_swap`
  (`formIntegrand … w v = conj (formIntegrand … v w)`), `formIntegrand_self_mk`
  (value `‖ℓ(π(g) v)‖²` at `gA`), `formIntegrand_self` (on the diagonal the integrand is a
  nonnegative real), `formIntegrand_add_left`, `formIntegrand_smul_left`,
  `continuous_formIntegrand`, `integrable_formIntegrand`.
- `exists_smoothDual_eq_one`: a nonzero vector of a smooth representation has a smooth
  functional with value `1` on it.
- Properties of `invariantForm`: `invariantForm_add_left`, `invariantForm_smul_left` (linear in
  `v`), `invariantForm_swap` (`(w, v) = conj (v, w)`), `invariantForm_rho`
  (`(π(g) v, π(g) w) = (v, w)`), `invariantForm_self` (`(v, v)` is the real number
  `∫ Re (formIntegrand … v v)`), `invariantForm_self_re_pos` (`(v, v) > 0` if `ℓ(v) ≠ 0`),
  `formFunctional_apply`.
- `invariantForm_self_re_pos_of_ne_zero` (**unitarity**, the first half of Lemma III.1.3 for
  irreducible `π`): if `π` is irreducible and `ℓ ≠ 0`, then `(v, v) > 0` for every `v ≠ 0`.
  With `invariantForm_swap`, `invariantForm_rho` and the linearity lemmas, `invariantForm` is a
  `G`-invariant positive definite Hermitian form on `V`; `invariantPositiveForm` packages it.
- `norm_character_eq_one`: for irreducible `π` with `hsq`, `‖χ(a)‖ = 1` for all `a ∈ A`.
- `isUnitarizable_of_isSquareIntegrable` (**unitarity**, Lemma III.1.3 for irreducible `π`):
  `IsUnitarizable π`.
- `exists_orthogonalityIntegral_eq_mul`: for irreducible `π` there is `κ : ℂ` with
  `I(v₁, ℓ₁, v₂, ℓ₂) = κ ℓ₂(v₁) ℓ₁(v₂)` for all `v₁, ℓ₁, v₂, ℓ₂`.
- `exists_formalDegree` (**III.1 (3)**): for irreducible `π` there is a real `d > 0` with
  `I(v₁, ℓ₁, v₂, ℓ₂) = d⁻¹ ℓ₂(v₁) ℓ₁(v₂)`, i.e. `d⁻¹ ⟨v₁, v̌_2⟩ ⟨v₂, v̌_1⟩` in the source's
  notation.
- `formalDegree_unique`: two reals `d`, `d'` satisfying this formula are equal.
- `formalDegree_pos`, `orthogonalityIntegral_eq_formalDegree`: `formalDegree` is positive and
  satisfies the formula of III.1 (3).

## Proof notes

- **Convergence.** Waldspurger deduces it from Cor. III.1.2 and Lemma II.1.5. Here it follows
  directly from the definition of square integrability: `‖integrand(gA)‖` is
  `N₁(gA) N₂((gA)⁻¹)` with `N_i = centralSubgroupCoefficientNorm`. Both factors are in `L²(μ)`,
  the second because `μ` is invariant under inversion
  (`MemLp.comp_measurePreserving`, `Measure.measurePreserving_inv`), so their product is
  integrable (`MemLp.integrable_mul` with the Hölder triple `(2, 2, 1)`). The integrand is
  continuous because coefficients of smooth representations are locally constant.
- **Invariance.** Right translation by `hA` turns the integrand of
  `I(v₁, ℓ₁, v₂, π̃₂(h⁻¹) ℓ₂)` into that of `I(π₁(h) v₁, ℓ₁, v₂, ℓ₂)`; the integrals agree by
  `integral_mul_right_eq_self_of_inv` (right invariance from left invariance and inversion
  invariance). Left translation by `h⁻¹A` gives the second law, by left invariance.
- **Intertwiners.** These laws are exactly the hypothesis of the Library's
  `exists_intertwiningMap_of_weakForm_of_compact_cofinal` (it uses `hcof` and admissibility of
  the target), applied to `orthogonalityFormLeft` and `orthogonalityFormRight`.
- **(2).** For irreducible inequivalent `π₁`, `π₂`, Mathlib's instance makes the type of
  intertwiners `π₁ → π₂` a subsingleton, so `T = 0` and `I = ℓ₂(0) = 0`.
- **The Schur step.** For `π₁ = π₂ = π`, `admissibleSchur_scalarEndomorphism` makes both
  intertwiners scalars: `I = c(ℓ₁, v₂) ℓ₂(v₁) = c'(v₁, ℓ₂) ℓ₁(v₂)`. With `v₀ ≠ 0`
  (irreducible representations are nonzero) and `ℓ₀(v₀) = 1` (`exists_smoothDual_eq_one`, from
  injectivity of the map into the smooth bidual), `c(ℓ₁, v₂) = κ ℓ₁(v₂)` with
  `κ = c'(v₀, ℓ₀)`.
- **Positivity.** `|χ| = 1` by `norm_character_eq_one`. Let `(·,·) = invariantForm … ℓ₀` and `ℓ_v = formFunctional … ℓ₀ v₀`.
  By invariance and the Hermitian symmetry, `(π(g⁻¹) v₀, v₀) = conj (π(g) v₀, v₀)`. Hence the
  integrand of `I(v₀, ℓ_v, v₀, ℓ_v)` is `|(π(g) v₀, v₀)|² ≥ 0`, continuous, and equal to
  `r² > 0` at the identity coset, where `r = (v₀, v₀) > 0` (`invariantForm_self_re_pos`, since
  `ℓ₀(v₀) = 1`). An open set of positive Haar measure gives `I(v₀, ℓ_v, v₀, ℓ_v) = s > 0`, real.
  The Schur step gives `I(v₀, ℓ_v, v₀, ℓ_v) = κ r²`. Hence `κ = s / r²` and `d = r² / s > 0`.
- **Unitarity.** `|χ| = 1` (`norm_character_eq_one`) holds because `π(a) v₀` is both `χ(a) v₀`
  and the value of the unitary central character of `hsq` on `a`. For `v ≠ 0`, the published
  `eq_zero_of_matrixCoefficient_vanishes` (irreducibility and `ℓ ≠ 0`) gives `g` with
  `ℓ(π(g) v) ≠ 0`. Then `(v, v) = (π(g) v, π(g) v) > 0`. Waldspurger's form lives on `V̌'` and
  sums over generators of a finitely generated `V'`. The variant here, on `V` with one
  functional, is derived and covers only irreducible `π`.

## Relation to the Library

- `IsSquareIntegrableModCentralSubgroup` (Worker 200's `CentralSubgroupCoefficients`) is used
  as the definition of square integrability. The published
  `CentralSubgroupComparisonStatement`, with its proof
  `centralSubgroupSquareIntegrabilityComparison`, compares it, for a closed central subgroup
  `A` with compact quotient in the center, with square integrability modulo the full center.
- The unitarity result is stated with the Library's `InvariantPositiveForm` and
  `IsUnitarizable` (`Representation/Unitary/Basic`, Worker 23). The published
  `admissibleUnitarySemisimplicity` (`Representation/Unitary/AdmissibleSemisimplicityProof`)
  proves that admissible unitarizable representations are semisimple when every open subgroup
  contains a compact open one; together with a proof of unitarity for every square integrable
  admissible representation it would give the second half of Lemma III.1.3.
- The published `squareIntegrableUnimodularUnitarity` (`Representation/Unitary/SquareIntegrableProof`)
  proves unitarizability of irreducible representations square integrable modulo the full
  center `Z(G)`, by the form `coefficientProductForm` built from
  `UnitaryCentralCharacter.coefficientProduct` on `G ⧸ Z(G)`. It needs a Hausdorff, locally
  compact, second countable `G` and a right invariant Haar measure on `G ⧸ Z(G)`. It does not
  apply to square integrability modulo an arbitrary central `A` such as `A_G`, which is the
  setting here, so the form on `G ⧸ A` is constructed in this module; its helper lemmas
  `exists_smoothDual_apply_ne_zero_of_compact_cofinal` and
  `eq_zero_of_matrixCoefficient_vanishes` are reused.
- `Langlands.CompactCoefficientClass.invariantForm` (`Representation/CompactCoefficient/FixedLevelFiniteness`)
  is a different invariant Hermitian form, for representations with compactly supported
  coefficients and an integral over `G` itself; it is not reused here.
- No Lean formulation of the relations III.1 (2), (3) or of a formal degree was found elsewhere
  in the Library. The Markdown of `TemperedDiscreteSeriesIsotypicStatement` mentions these
  relations as background for its route. The `CompactCoefficient` modules prove orthogonality
  of isotypic projectors, which is a different statement.

## Open obligations

- The identification of `A` with Waldspurger's `A_G`, of `μ` with his measure on `A_G \ G`, and
  the unimodularity of `G / A_G` and the hypothesis `hcof` for actual reductive `p`-adic groups.
- Lemma III.1.3 for reducible square integrable representations (unitarity, and hence
  semisimplicity via `admissibleUnitarySemisimplicity`).
- Corollary III.1.2 and Lemma II.1.5, which Waldspurger uses for the convergence, are not
  needed here and are not formalized by this module.
