# The coefficient spaces `A(G)` and `A^w(G)` (Waldspurger, Lemma I.6.1 and Lemma III.2.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.AdmissibleCoefficientSpace`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence`:
  `coefficientFunctionSpace` (Waldspurger's `A(π)`, the span of the coefficients
  `g ↦ ℓ(π(g) x)` with `ℓ` smooth), `matrixCoefficient_mem_coefficientFunctionSpace`,
  `coefficientIntertwiningMap`; through it `Whittaker.rightTranslation` (right translation on
  `G → ℂ`), `IsBiInvariant`, `smoothDualFixedRestriction_bijective` (restriction of
  `K`-fixed smooth functionals to `V^K` is bijective for `K` compact open);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations`: `translate`
  (`translate g₁ g₂ f = (x ↦ f(g₂⁻¹ x g₁))`), `translate_one_one`, `mem_conjSubgroup`,
  `CompactOpenSubgroup.conj`, `CompactOpenSubgroup.inf`, `TranslationWeights`,
  `TranslationWeights.nu_translate_le` (Lemma II.1.2 on seminorms);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzAction`:
  `HasTemperedCoefficients`, `CompactOpenSubgroup.cofinal`; through it `TemperedPairing`
  (`HasTemperedGrowth`, `hasTemperedGrowth_iff`, `HasTemperedGrowth.add`,
  `HasTemperedGrowth.smul`);
- `Langlands.Representation.Compact.ProjectionProof` (`averageMap`,
  `averageMap_mem_fixedVectors`, `averageMap_id`, `averageMap_commute`, `finite_orbit_of_smooth`,
  `orbit`, `orbitMean`) and `Langlands.Representation.Jacquet.CharacterAveraging`
  (`Jacquet.Localization.orbitMean_mem`, `Jacquet.Localization.orbitMean_eq_smul_sum`);
- `Langlands.Representation.FiniteVectors` (`FiniteVectors.orbitSubrepresentation`, the span of
  the orbit of a vector, and `FiniteVectors.action_mem_orbitSpan`);
- `Langlands.Representation.Smooth.Admissibility.EmbeddingProof` (`isAdmissible_of_injective`),
  `Langlands.Representation.Unramified.SphericalConstituentExistenceProof`
  (`SphericalExistence.isAdmissible_of_surjective`; through it `finite_fixedVectors_of_le`),
  `Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions`
  (`ProductFactorization.subrepresentationInclusion`).

From Mathlib it uses `Subspace.dualCoannihilator_dualAnnihilator_eq`,
`Submodule.dualAnnihilator_bot`, `Module.dual_finite`, `Submodule.iSup_induction`,
`Submodule.span_induction`, `Submodule.map_span`, `Submodule.mem_sup` and
`Submodule.finiteDimensional_of_le`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quoted text carries no overline (checked on the rendered PDF pages 15 and
31).

- I.6, printed p. 249 (PDF p. 15): "Considérons l'espace `C_lisse(G) = ⋃_H C(H \ G/H)`, où `H`
  parcourt l'ensemble des sous-groupes ouverts compacts de `G`. [...] Pour `f ∈ C_lisse(G)`,
  notons `V_ρ(f)`, resp. `V_λ(f)`, resp. `V_{ρ×λ}(f)`, le plus petit sous-espace de
  `C_lisse(G)` contenant `f` et stable par `ρ`, resp. `λ`, resp. `ρ × λ`. Notons `ρ_f`, resp.
  `λ_f`, la représentation déduite de `ρ` dans `V_ρ(f)`, resp. de `λ` dans `V_λ(f)`. Notons
  `A_ρ`, resp. `A_λ`, l'ensemble des `f ∈ C_lisse(G)` telles que `ρ_f`, resp. `λ_f`, soit
  admissible. D'autre part, pour toute représentation admissible `π` de `G`, notons `A(π)` le
  sous-espace de `C_lisse(G)` engendré par les coefficients de `π`. Posons
  `A(G) = ⋃_π A(π) = Σ_π A(π)`, où `π` parcourt l'ensemble des classes de représentations
  admisibles de `G`."
- Lemme I.6.1, printed p. 249: "(1) Soit `f ∈ A_ρ`, resp. `A_λ`. Alors `V_{ρ×λ}(f) = A(ρ_f)`,
  resp. `= A(λ̌_f)`. (2) On a l'égalité `A_ρ = A_λ = A(G)`." Its proof shows that the forms
  `v_g = (f' ↦ f'(g))` span the smooth dual of `V_ρ(f)` ("Il résulte de (i) et (ii) que
  `V = V_ρ(f)ˇ`").
- III.2, printed p. 265 (PDF p. 31): "Notons `C^w_lisse(G)` le sous-espace des
  `f ∈ C_lisse(G)` pour lesquelles il existe `c > 0` et `r ∈ ℝ` tels que pour tout `g ∈ G`,
  `|f(g)| ⩽ c Ξ(g)(1 + σ(g))^r`. On pose `A^w(G) = A(G) ∩ C^w_lisse(G)`. Soit `(π, V)` une
  représentation admissible de `G`. On dit que `π` est tempérée si `A(π) ⊂ A^w(G)`." and
  "Lemme III.2.1. On a les égalités `A^w(G) = ⋃_π A(π) = Σ_π A(π)`, où `π` parcourt les
  représentations admissibles tempérées de `G`."

## Correspondence and generalizations

- `G` is a topological group; from `isAdmissible_sup` on it has a compact open subgroup
  (`[Nonempty (CompactOpenSubgroup G)]`), which makes every open subgroup contain a compact open
  one. Functions are all of `G → ℂ`, not only `C_lisse(G)`.
- `ρ` is `Whittaker.rightTranslation ℂ G`, `V_ρ(f)` is `rightTranslateSpan f` (the orbit span
  `FiniteVectors.orbitSubrepresentation`), `ρ_f` is its representation, bundled as
  `rightTranslateRep hf` when `f ∈ A_ρ`. `V_{ρ×λ}(f)` is `twoSidedTranslateSpan f`, the span of
  the translates `x ↦ f(g₂⁻¹ x g₁)`.
- `A_ρ` is `IsRightAdmissible f`: `f` is bi-invariant under a compact open subgroup (the
  condition `f ∈ C_lisse(G)`) and `ρ_f` is admissible.
- `A(π)` is the Library's `coefficientFunctionSpace`. `A(G)` is expressed as the union: `f`
  lies in `A(A)` for some admissible `A : SmoothRep.{0, u, u} ℂ G`, i.e. on a carrier in the
  universe of `G`, rather than over all classes of admissible representations.
  `exists_admissible_coefficient_add` shows that this union is closed under addition, which is
  the source's `⋃ = Σ`.
- "Tempered" is the Library's `HasTemperedCoefficients Ξ σ`, the tempered growth of the
  coefficients `g ↦ ℓ(π(g) v)`, and `C^w_lisse(G)` is replaced by the functions with
  `HasTemperedGrowth Ξ σ` (`∃ c r, ‖f(g)‖ ≤ c Ξ(g)(1 + σ(g))^r`; neither smoothness nor `c > 0`
  is required). Lemma II.1.2 enters as `TranslationWeights Ξ σ`.
- The statements for left translation (`A_λ`, `λ_f` and `A(λ̌_f)` in Lemma I.6.1) are not
  formalized.
- Derived results, not statements of the paper: `rightTranslation_apply'`,
  `rightTranslation_mem_rightTranslateSpan`, `mem_rightTranslateSpan_self`,
  `leftInvariant_of_mem_rightTranslateSpan`, `evalFunctional`, `evalFunctional_apply`,
  `isSmoothVector_evalFunctional`, `map_orbitMean_of_forall_eq`,
  `translate_mem_twoSidedTranslateSpan`, `orbitSpanMap`, `orbitSpanMap_surjective`,
  `inclusionOfLe`, `inclusionOfLe_injective`, `isAdmissible_sup`,
  `isRightAdmissible_matrixCoefficient`, `isRightAdmissible_zero`, `isRightAdmissible_smul`,
  `isRightAdmissible_add`, `isRightAdmissible_of_mem_coefficientFunctionSpace`,
  `HasTemperedGrowth.translate`, `hasTemperedGrowth_of_mem_twoSidedTranslateSpan`,
  `hasTemperedGrowth_of_mem_coefficientFunctionSpace`.

## Scope and hypotheses

- Section `RightTranslates`: `G : Type u` a group; from `IsRightAdmissible` on, a topological
  group. `leftInvariant_of_mem_rightTranslateSpan` takes a subgroup `H` with
  `f(h x) = f(x)` for `h ∈ H`. `isSmoothVector_evalFunctional` takes a compact open `H` with
  that property and `x : G`.
- Section `Averaging`: `map_orbitMean_of_forall_eq` takes a group `K`, `τ : Representation ℂ K X`
  with a finite orbit of `v`, a linear form `φ` and `c` with `φ(τ(k) v) = c` for all `k`.
- Section `Evaluations`: `G` a topological group. `mem_span_evalFunctional`,
  `twoSidedTranslateSpan_eq_coefficientFunctionSpace` take `hf : IsRightAdmissible f`.
- Section `Admissibility`: `orbitSpanMap`, `orbitSpanMap_surjective`, `inclusionOfLe` and
  `inclusionOfLe_injective` hold for any group. With `[Nonempty (CompactOpenSubgroup G)]`:
  `isAdmissible_sup` (two admissible subrepresentations of any representation `σ`),
  `isRightAdmissible_matrixCoefficient` (`ρ` admissible, `ℓ` smooth), `isRightAdmissible_zero`,
  `isRightAdmissible_add`, `isRightAdmissible_of_mem_coefficientFunctionSpace` (`A` admissible),
  `isRightAdmissible_iff`, `exists_admissible_coefficient_add`; `isRightAdmissible_smul` needs
  neither.
- Section `Tempered`: weights `Ξ σ : G → ℝ` with `hw : TranslationWeights Ξ σ`
  (`Ξ > 0`, `σ ≥ 0`, Lemma II.1.2 and the translation bound for `σ`);
  `temperedCoefficient_iff` and `exists_tempered_coefficient_add` also take
  `[Nonempty (CompactOpenSubgroup G)]`.

## Definitions

- `rightTranslateSpan f` (`V_ρ(f)`), `twoSidedTranslateSpan f` (`V_{ρ×λ}(f)`),
  `IsRightAdmissible f` (`f ∈ A_ρ`), `rightTranslateRep hf` (`ρ_f`).
- `evalFunctional f x`: evaluation at `x` as a linear form on `V_ρ(f)` (the source's `v_x`).
- `orbitSpanMap Φ x`: the restriction of an intertwiner `Φ` to the orbit spans of `x` and
  `Φ x`; `inclusionOfLe h`: the inclusion `W₁ → W₂` of subrepresentations with `W₁ ≤ W₂`.

## Results

- `isSmoothVector_evalFunctional`: `v_x` is smooth, fixed by `x⁻¹ H x`.
- `mem_span_evalFunctional` (**the step `V = V_ρ(f)ˇ` of the proof of Lemma I.6.1**): for
  `f ∈ A_ρ`, every smooth linear form on `V_ρ(f)` is a finite linear combination of the `v_x`.
- `twoSidedTranslateSpan_eq_coefficientFunctionSpace` (**Lemma I.6.1 (1) for `ρ`**):
  `V_{ρ×λ}(f) = A(ρ_f)` for `f ∈ A_ρ`.
- `isAdmissible_sup`: the sum of two admissible subrepresentations is admissible.
- `isRightAdmissible_matrixCoefficient`, `isRightAdmissible_zero`, `isRightAdmissible_smul`,
  `isRightAdmissible_add`, `isRightAdmissible_of_mem_coefficientFunctionSpace`: `A_ρ` contains
  the coefficients of admissible representations and is a subspace, hence contains every `A(π)`.
- `isRightAdmissible_iff` (**Lemma I.6.1 (2) for `ρ`**): `A_ρ = A(G)`.
- `exists_admissible_coefficient_add`: `⋃_π A(π)` is closed under addition.
- `HasTemperedGrowth.translate`, `hasTemperedGrowth_of_mem_twoSidedTranslateSpan`,
  `hasTemperedGrowth_of_mem_coefficientFunctionSpace`: tempered growth passes to two-sided
  translates, to `V_{ρ×λ}(f)`, and to `A(π)` for `π` with tempered coefficients.
- `temperedCoefficient_iff` (**Lemma III.2.1, union**): `f ∈ A(G)` with tempered growth iff
  `f ∈ A(π)` for an admissible `π` with tempered coefficients.
- `exists_tempered_coefficient_add` (**Lemma III.2.1, sum**): that union is closed under
  addition.

## Proof notes

1. `isSmoothVector_evalFunctional`: elements of `V_ρ(f)` are left `H`-invariant
   (`leftInvariant_of_mem_rightTranslateSpan`), so `v_x(ρ(k⁻¹) v) = v(x k⁻¹) = v(x)` when
   `x k⁻¹ x⁻¹ ∈ H`.
2. `mem_span_evalFunctional`: let `E` be the span of the `v_x` in the smooth dual; it is stable
   under the contragredient (`ρ̌(g) v_x = v_{x g⁻¹}`). For a smooth `ℓ`, choose a compact open
   `K` fixing it. The `K`-average `P` of the smooth dual maps `E` into `E`
   (`orbitMean_mem`) and satisfies `(P e)(w) = e(w)` for `w ∈ V_ρ(f)^K`
   (`map_orbitMean_of_forall_eq`). The restrictions of the `P(v_x)` to the finite-dimensional
   `V_ρ(f)^K` separate its points (a function vanishing at every `x` is `0`), so they span its
   dual (`Subspace.dualCoannihilator_dualAnnihilator_eq`). Hence `ℓ` and some `P e`, `e ∈ E`,
   have the same restriction, and are equal by `smoothDualFixedRestriction_bijective`.
3. `twoSidedTranslateSpan_eq_coefficientFunctionSpace`: `x ↦ f(g₂⁻¹ x g₁)` is the coefficient
   of `ρ_f` at `ρ(g₁) f` and `v_{g₂⁻¹}`; conversely, by step 2 every coefficient
   `g ↦ ℓ(ρ_f(g) v)` is a combination of the functions `g ↦ v(x g)`, which lie in
   `V_{ρ×λ}(f)` (`translate_mem_twoSidedTranslateSpan`).
4. `isAdmissible_sup`: vectors of `W₁ + W₂` are sums of smooth vectors. For a compact open `K`,
   a `K`-fixed `v = a + b` equals `P a + P b` with `P` the `K`-average, and `P a`, `P b` are
   `K`-fixed in `W₁`, `W₂` (`averageMap_commute` with the inclusions), so `(W₁ + W₂)^K` lies in
   the image of `W₁^K × W₂^K`.
5. `isRightAdmissible_matrixCoefficient`: bi-invariance under a compact open subgroup of the
   subgroups fixing `x` and `ℓ`; `ρ_f` is the image of the orbit span of `x` (admissible as a
   subrepresentation of `ρ`) under `coefficientIntertwiningMap` (`orbitSpanMap_surjective`,
   `isAdmissible_of_surjective`).
6. `isRightAdmissible_add`: `V_ρ(f₁ + f₂) ⊂ V_ρ(f₁) + V_ρ(f₂)` and step 4;
   `isRightAdmissible_iff`: `f = translate 1 1 f ∈ V_{ρ×λ}(f) = A(ρ_f)` (step 3), and
   conversely `Submodule.iSup_induction` over `A(π)` with steps 5, 6.
7. `temperedCoefficient_iff`: for `f ∈ A(G)` of tempered growth, `f ∈ A_ρ`, the coefficients of
   `ρ_f` lie in `A(ρ_f) = V_{ρ×λ}(f)`, whose elements have tempered growth
   (`HasTemperedGrowth.translate` from `TranslationWeights.nu_translate_le`); conversely the
   elements of `A(π)` are finite sums of tempered coefficients.
