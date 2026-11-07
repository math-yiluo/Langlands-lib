# Normalized induction preserves temperedness (Waldspurger, Lemma III.2.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedTemperedCoefficients`,
namespace `Langlands.HarishChandraSchwartz`. It imports `InducedFourierTransform` (which brings in
`InducedCoefficientXi`, `InducedCoefficientBound`, `SphericalLevi`, `LeviWeightIntegrability`,
`SchwartzAction` and Worker 200's `CompactProductInducedCoefficients`,
`CompactProductCoefficientBounds` and `CompactCoefficientHaarComparison`) and `ConstantTermBound`
(for `SigmaProductBound`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

III.2, printed p. 265 (PDF p. 31): "Notons `C^w_lisse(G)` le sous-espace des
`f ∈ C_lisse(G)` pour lesquelles il existe `c > 0` et `r ∈ ℝ` tels que pour tout `g ∈ G`,
`|f(g)| ⩽ c Ξ(g)(1 + σ(g))^r`. On pose `A^w(G) = A(G) ∩ C^w_lisse(G)`. Soit `(π, V)` une
représentation admissible de `G`. On dit que `π` est tempérée si `A(π) ⊂ A^w(G)`."

Lemma III.2.3, printed p. 266 (PDF p. 32): "Soient `P = MU` un sous-groupe parabolique
semi-standard de `G` et `(π, V)` une représentation admissible tempérée de `M`. Alors la
représentation `(I_P^G π, I_P^G V)` de `G` est tempérée."

Waldspurger's proof (printed pp. 266–267) reduces to `P` standard and uses the exponent
criterion of Proposition III.2.2 together with the computation of the Jacquet modules
`(I_P^G π)_{P'}` in I.3.

Lemma II.3.1, printed p. 254 (PDF p. 20): "Soit `P = MU` un sous-groupe parabolique
semi-standard de `G`. Il existe `C_1, C_2 > 0` tels que pour tous `m ∈ M`, `u ∈ U`, on ait
`C_1(1 + σ(mu)) ⩽ 1 + sup(σ(m), σ(u)) ⩽ C_2(1 + σ(mu))`."

Lemma II.1.6, printed p. 252 (PDF p. 18): "Pour tout `g ∈ G`, on a l'égalité
`Ξ(g) = ∫_K δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg)) dk`."

I.1, printed p. 242 (PDF p. 8): `‖k_1 g k_2‖ = ‖g‖` for `k_1, k_2 ∈ K`, and
`σ(g) = log ‖g‖`; so Waldspurger's `σ` is invariant under `K` on both sides and `σ ≥ 0`.

## Route

The Lean proof does not follow Waldspurger's exponent argument. It bounds the coefficients of
`I_P^G π` directly, by the route of the proofs of Corollary III.1.2 and Lemma VI.2.2 (printed
pp. 298–299) as formalized in `InducedCoefficientXi`: a coefficient of `I_P^G π` at `g` is
`∫_K δ_P^{1/2}(m_P(kg)) ⟨π(m_P(kg)) v(k_P(kg)), v̌(k)⟩ dk`; the vectors `v(k_P(kg))` and
`v̌(k)` stay in finite-dimensional spaces, so temperedness of `π` gives one bound
`c Ξ^M(m) (1 + σ_M(m))^R` for the integrand coefficient at `m = m_P(kg)`; the bound
`σ_M(m_P(q)) ≤ c (1 + σ(q k))` (from Lemma II.3.1 when `σ_M = σ|_M`) replaces
`(1 + σ_M(m_P(kg)))^R` by a multiple of `(1 + σ(kg))^R = (1 + σ(g))^R`, and Lemma II.1.6 turns
the remaining integral into `Ξ(g)`. This route is derived, not taken from the source's proof of
Lemma III.2.3.

## Scope: data and explicit hypotheses

The group and induction data are those of `InducedCoefficientXi` and of Worker 200's
`CompactProductInducedCoefficients`: a locally compact nonarchimedean group `G`, subgroups `P`,
`M`, `U` with `h : IsSemidirectDecomposition P M U` (`P = M ⋉ U`, `m_P = h.projection`),
`hU : IsClosed (U : Set G)`, a smooth complex representation `A : SmoothRep ℂ M` (Waldspurger's
`(π, V)`), and a compact open subgroup `K : OpenSubgroup G` with `hK : IsCompact (K : Set G)`.
The normalized induced representation is `(normalizedInductionFunctor h hU).obj A`.

The weight data are those of `SphericalLevi`: a subgroup `P₀` with characters
`δ₀ : P₀ →* ℝ≥0ˣ` and `δ₀M : P₀ ∩ M →* ℝ≥0ˣ`; `Ξ = xi hP₀K δ₀` and `Ξ^M = xi hMK δ₀M`. The
character `δ_P` is the Haar modulus
`HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer` of the conjugation action of
`M` on `U`. The functions `σ : G → ℝ` and `σ_M : M → ℝ` are arbitrary real functions subject to
the hypotheses listed below.

"Tempered" is the Library predicate `HasTemperedCoefficients Ξ σ ρ` of `SchwartzAction`: for
every vector `v` and smooth functional `ℓ` there are `c`, `r` with
`|ℓ(ρ(g) v)| ≤ c Ξ(g) (1 + σ(g))^r` for all `g` (`HasTemperedGrowth`). This is Waldspurger's
`A(π) ⊂ A^w(G)`: coefficients of smooth representations are smooth, so only the growth condition
carries content. Admissibility of `π` is the hypothesis `hA : A.IsAdmissible`.

Hypotheses of each theorem (every explicit argument and instance):

- `leviSigmaBound_of_sigmaProductBound`: `[Group G]`, subgroups `P M U`,
  `h : IsSemidirectDecomposition P M U`, a set `K : Set G`, `σ : G → ℝ`,
  `hσU : SigmaProductBound M U σ` (there is `C > 0` with
  `C (1 + max (σ m) (σ u)) ≤ 1 + σ(m u)` for `m ∈ M`, `u ∈ U`: the second inequality of
  Lemma II.3.1 with `C = 1/C_2`), and `hσK' : ∀ g, ∀ k ∈ K, σ (g * k) = σ g` (right
  `K`-invariance).
- `LeviData.norm_compactIntegral_le_xi_mul_rpow`: `[Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]`,
  subgroups `K P₀ P M` with `[CompactSpace K] [CompactSpace (K.subgroupOf M)]`, characters
  `δ₀ δP δ₀M`, a homomorphism `mP : P →* M`; `hL : LeviData K P₀ P M δ₀ δP δ₀M mP`,
  `hK : IsOpen (K : Set G)`, `hP₀K : IsIwasawaPair P₀ K`,
  `hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M)`,
  `hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1`, `σ : G → ℝ` with
  `hσK : ∀ k ∈ K, ∀ g, σ (k * g) = σ g` (left `K`-invariance), `Φ : K → G → ℂ`, reals `C`, `r`
  (no sign conditions), `hΦ : ∀ k x, ‖Φ k x‖ ≤ C * leviXiWeight … x * (1 + σ x) ^ r`, and
  `g : G`.
- `exists_coefficientTensorMap_le_rpow_of_tensor`: `[Group L] [TopologicalSpace L]
  [IsTopologicalGroup L]`, `A : SmoothRep ℂ L`, `ξ σL : L → ℝ`, `hξ : ∀ m, 0 ≤ ξ m`,
  `hσL : ∀ m, 0 ≤ σL m`, `hT : HasTemperedCoefficients ξ σL A.representation`, and
  `t : CoefficientTensor A`.
- `exists_coefficientTensorMap_le_rpow`: the same data, `hξ`, `hσL`, `hT`, a set
  `S : Set (CoefficientTensor A)` and `hS : S.Finite`.
- `norm_inducedIntegrandKernel_le_rpow`: `[Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace ((K : Subgroup G).subgroupOf M)]`; `h`,
  `hU`, `A`, `K`, `hK`; `hδ : IsUnimodularModulus U hU` (`U` unimodular);
  `hL : LeviData K P₀ P M δ₀ δ_P δ₀M h.projection` (`P₀ ⊆ P`, `M ⊆ P`, `m_P` is the identity on
  `M`, `ker m_P ⊆ P₀`, `δ₀` trivial on `ker m_P`, `δ₀ = δ_P δ₀^M` on `P₀ ∩ M`, `δ_P` trivial
  on `K ∩ M`); `hP₀K : IsIwasawaPair P₀ K` (`G = P₀ K`);
  `hMK : IsIwasawaPair (P₀ ∩ M) (K ∩ M)` (`M = (P₀ ∩ M)(K ∩ M)`); `σ : G → ℝ`, `σM : M → ℝ`
  with `hσ : ∀ g, 0 ≤ σ g`, `hσM : ∀ m, 0 ≤ σM m`, `hlevi : LeviSigmaBound h K σ σM`;
  `hT : HasTemperedCoefficients (xi hMK δ₀M) σM A.representation`; and
  `F : productInducedCoefficientObject h hU A`.
- `hasTemperedCoefficients_normalizedInduction_of_tempered`: the instances of the previous
  item together with `[T2Space G] [CompactSpace (K : Subgroup G)] [LocallyCompactSpace P]`;
  `h`, `hU`, `A`, `K`, `hK`; the hypotheses of `CompactInduction.coefficientMap`:
  `hP : IsClosed (P : Set G)`, `hm : Continuous h.projection`,
  `hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q * k` (`G = P K`),
  `hG : ∀ g, Measure.modularCharacter g = 1` (`G` unimodular),
  `hδP : ∀ q : P, Measure.modularCharacter q = closedRestrictCharacter U hU P … q` (the modular
  character of `P` is the modulus of its action on `U`), `hA : A.IsAdmissible`; then `hδ`,
  `hL`, `hP₀K`, `hMK`, `hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1`, `hσ`, `hσM`,
  `hσK : ∀ k ∈ K, ∀ g, σ (k * g) = σ g`, `hlevi : LeviSigmaBound h K σ σM`, and
  `hT : HasTemperedCoefficients (xi hMK δ₀M) σM A.representation`.
- `hasTemperedCoefficients_normalizedInduction_of_sigmaProductBound`: the instances and the
  hypotheses `h`, `hU`, `A`, `K`, `hK`, `hP`, `hm`, `hPK`, `hG`, `hδP`, `hA`, `hδ`, `hL`, `hP₀K`,
  `hMK`, `hδ₀` of the previous item; `σ : G → ℝ` with `hσ : ∀ g, 0 ≤ σ g`,
  `hσK : ∀ k ∈ K, ∀ g, σ (k * g) = σ g`, `hσK' : ∀ g, ∀ k ∈ K, σ (g * k) = σ g`,
  `hσU : SigmaProductBound M U σ`; and
  `hT : HasTemperedCoefficients (xi hMK δ₀M) (fun m : M => σ m) A.representation`.

## Definitions

- `LeviSigmaBound h K σ σM`: there is `c : ℝ` with `σ_M(m_P(q)) ≤ c (1 + σ(q k))` for all
  `q ∈ P` and `k ∈ K`, where `m_P = h.projection`. This is a derived hypothesis, not a notion of
  the source; for `σ_M = σ|_M` it follows from Lemma II.3.1 and the right `K`-invariance of `σ`.

## Results

- `leviSigmaBound_of_sigmaProductBound`: `LeviSigmaBound h K σ (fun m => σ m)` from `hσU` and
  `hσK'`.
- `LeviData.norm_compactIntegral_le_xi_mul_rpow` (analytic core): under `hΦ`,
  `‖compactIntegral K Φ g‖ ≤ C Ξ(g) (1 + σ(g))^r`.
- `exists_coefficientTensorMap_le_rpow_of_tensor`: there are `C ≥ 0`, `R ≥ 0` with
  `‖coefficientTensorMap A t m‖ ≤ C (ξ(m) (1 + σL(m))^R)` for every `m`.
- `exists_coefficientTensorMap_le_rpow`: there are `C > 0`, `R ≥ 0` with this bound for every
  `t ∈ S` and every `m`.
- `norm_inducedIntegrandKernel_le_rpow` (integrand bound): there are `C > 0`, `R ≥ 0` with
  `‖inducedIntegrandKernel h hU A K F k x‖ ≤ C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x)) (1 + σ(x))^R` for
  all `k ∈ K`, `x ∈ G`, in the form `C * leviXiWeight … x * (1 + σ x) ^ R`, where `m_P(x)` is the
  Levi component of the factorization `x = q k₁` chosen by `iwasawaFactor`.
- `hasTemperedCoefficients_normalizedInduction_of_tempered` (**Lemma III.2.3**):
  `HasTemperedCoefficients (xi hP₀K δ₀) σ ((normalizedInductionFunctor h hU).obj A).representation`.
- `hasTemperedCoefficients_normalizedInduction_of_sigmaProductBound` (**Lemma III.2.3 for
  `σ_M = σ|_M`**): the same conclusion.

## Proof notes

`leviSigmaBound_of_sigmaProductBound`: for `q ∈ P` write `q = m u` with `m = m_P(q)` and
`u = m⁻¹ q ∈ U` (`h.projection_inv_mul_mem`). `hσU` gives
`C (1 + σ(m)) ≤ C (1 + max (σ m) (σ u)) ≤ 1 + σ(q)`, so `σ(m) ≤ 1 + σ(m) ≤ C⁻¹ (1 + σ(q))`, and
`σ(q) = σ(q k)` by `hσK'`; the constant is `c = C⁻¹`.

`LeviData.norm_compactIntegral_le_xi_mul_rpow`: by `hσK`, `σ(k g) = σ(g)`, so `hΦ` at
`x = k g` bounds the integrand by `C (1 + σ(g))^r δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg))`. The weight
`k ↦ leviXiWeight … (k g)` is integrable for the probability Haar measure on `K` because its
integral is `Ξ(g)` (`LeviData.xi_eq_integral`, Lemma II.1.6), which is positive (`xi_pos`), hence
nonzero; `norm_integral_le_of_norm_le` and `LeviData.xi_eq_integral` give the bound.

`exists_coefficientTensorMap_le_rpow_of_tensor`: induction on the tensor. For `v ⊗ ℓ`,
`coefficientTensorMap_tmul` and `hT v ℓ` give `c`, `r`; replacing them by `max c 0`, `max r 0`
uses `ξ ≥ 0` and `1 + σL ≥ 1`. For a sum, add the constants and take the larger exponent.
`exists_coefficientTensorMap_le_rpow`: choose constants for each tensor and bound them over the
finite set `S` (with `max 1 B` and `max 0 D`).

`norm_inducedIntegrandKernel_le_rpow`: apply `exists_coefficientTensorMap_le_rpow` with
`ξ = Ξ^M` (nonnegative, an integral of the nonnegative `iwasawaWeight`) to the finite set of
compact values `CompactInduction.compactValue h hU A K F` (finite by Worker 200's
`compactValue_range_finite`), giving `C₀`, `R`. For `x ∈ G`, `exists_iwasawaFactor` writes
`x = q k₁` with `q = iwasawaFactor x`; Worker 200's `CompactInduction.integrand_factorization`
writes `Φ(k, x)` as `δ_P^{1/2}(q)` (`closedHalfCharacter`) times the coefficient of a compact
value at `m_P(q)`, and `closedHalfCharacter_eq_comp_projection` (using `hδ`) identifies the
absolute value of the first factor with `δ_P(m_P(q))^{1/2}`. With `c' = max c 0` from `hlevi`,
`1 + σ_M(m_P(q)) ≤ (1 + c')(1 + σ(x))` (using `σ ≥ 0`), so
`(1 + σ_M(m_P(q)))^R ≤ (1 + c')^R (1 + σ(x))^R`; the constant is `C₀ (1 + c')^R`.

`hasTemperedCoefficients_normalizedInduction_of_tempered`: for `v` and a smooth functional `ℓ`
of `I_P^G A`, let `E = CompactInduction.coefficientTensorEquiv …` and `F = E⁻¹(v ⊗ ℓ)`. As in
the Library's `hasTemperedCoefficients_normalizedInduction`, `coefficientMap … F g` is
`ℓ(I_P^G A(g) v)`; by `CompactInduction.coefficientMap_integral`,
`CompactInduction.measure_eq_normalizedHaar` and `inducedIntegrandKernel_mul` it equals
`compactIntegral K (inducedIntegrandKernel … F) g`. The integrand bound and the analytic core
give `|ℓ(I_P^G A(g) v)| ≤ C Ξ(g) (1 + σ(g))^R`.

`hasTemperedCoefficients_normalizedInduction_of_sigmaProductBound`: the previous theorem with
`σ_M = σ|_M`, `hσM` from `hσ`, and `hlevi` from `leviSigmaBound_of_sigmaProductBound`.

## Correspondence with the source

- Waldspurger's `(π, V)` is `A`, admissible by `hA`, tempered by `hT`; `I_P^G π` is
  `(normalizedInductionFunctor h hU).obj A`; "tempered" is `HasTemperedCoefficients` as above.
- Waldspurger defines `σ` on `G` (I.1) and writes `σ(m)` for `m ∈ M` (for instance in
  Lemma II.3.1); `hasTemperedCoefficients_normalizedInduction_of_sigmaProductBound` reads
  "tempered representation of `M`" with `σ_M = σ|_M` (this reading is ours).
  `hasTemperedCoefficients_normalizedInduction_of_tempered` allows any `σ_M ≥ 0` satisfying
  `LeviSigmaBound`. The hypotheses `hσK`, `hσK'` and `hσ` are I.1's `‖k_1 g k_2‖ = ‖g‖` and
  `‖g‖ ≥ 1`; `hσU` is Lemma II.3.1 for `P = M U`.
- The source states the lemma for a semi-standard parabolic subgroup; here `P = M ⋉ U` is
  abstract, and the parabolic structure enters only through `LeviData`, the Iwasawa pairs, the
  coefficient-map hypotheses and `SigmaProductBound`.

## Relation to the Library

- `InducedCoefficientXi` (`inducedIntegrandKernel`, `inducedIntegrandKernel_mul`,
  `norm_inducedIntegrandKernel_le`, `norm_coefficientMap_le_xi`) and `InducedCoefficientBound`
  (`compactIntegral`, `LeviData.norm_compactIntegral_le_xi`) are the bounded case
  (`hcoeff`, the conclusion of Corollary III.1.2 for `M`); this module proves the polynomially
  weighted versions.
- `InducedFourierTransform.hasTemperedCoefficients_normalizedInduction` derives tempered
  coefficients of `I_P^G A` from `hcoeff`; `hasTemperedCoefficients_normalizedInduction_of_tempered`
  derives them from temperedness of `A`, as in Lemma III.2.3.
- Worker 200's `coefficientTensorMap_bound` and `coefficientTensorMap_bound_finite`
  (`CompactProductCoefficientBounds`) are the bounded analogues of
  `exists_coefficientTensorMap_le_rpow_of_tensor` and `exists_coefficientTensorMap_le_rpow`.
- Defining modules of the cited Library declarations: `LeviData`, `leviComponent`,
  `LeviData.xi_eq_integral` and `IsIwasawaPair.mono` in `SphericalLevi`; `leviXiWeight` in
  `LeviWeightIntegrability`; `xi`, `xi_pos`, `exists_iwasawaFactor`, `iwasawaFactor`,
  `normalizedHaar` and `IsIwasawaPair` in `Spherical`; `SigmaProductBound` in
  `ConstantTermBound`; `HasTemperedCoefficients` in `SchwartzAction`; `HasTemperedGrowth` in
  `TemperedPairing`; `compactValue`, `compactValue_range_finite` and `integrand_factorization`
  in `Langlands.Representation.Plancherel.CompactProductCoefficientBounds`;
  `coefficientTensorEquiv`, `coefficientMap` and `coefficientMap_integral` in
  `Langlands.Representation.Plancherel.CompactProductInducedCoefficients`;
  `measure_eq_normalizedHaar` in `Langlands.Representation.Plancherel.CompactCoefficientHaarComparison`;
  `closedHalfCharacter_eq_comp_projection` and `IsUnimodularModulus` in
  `Langlands.Representation.Aubert.General.Parabolic`; `coefficientTensorMap` and
  `coefficientTensorMap_tmul` in `Langlands.Representation.Plancherel.CoefficientTensors`.

## Open obligations

- The identification of the Library data (`K`, `P₀`, `δ₀`, `σ`) with Waldspurger's for an
  actual reductive group, and the verification there of the hypotheses `hL`, `hP₀K`, `hMK`,
  `hδ₀`, the coefficient-map hypotheses, `hσK`, `hσK'`, `hσ` and `hσU` (Lemma II.3.1).
- Waldspurger's exponent proof through Proposition III.2.2 and I.3 is not formalized.
