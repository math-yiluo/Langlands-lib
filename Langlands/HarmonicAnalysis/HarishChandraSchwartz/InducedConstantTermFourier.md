# The Fourier transform and the constant term (Waldspurger, Lemma VII.1.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourier`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierTransform`:
  `inducedFourierTransform` (`f ↦ f̂(ω, P)` on `L(ω, P)`), Lemma VII.1.1 (ii) for `G` and the
  uniqueness statement `inducedFourierTransform_eq_of_forall_integral`. Through its imports it
  also supplies the generic `coefficientFourierTransform` with
  `coefficientFourierTransform_translate` and `integral_conj_coefficientTensorMap_mul_eq_inner`
  (Lemma VII.1.1 for any admissible representation, used here for `M`), Worker 200's
  `productInducedCoefficientObject` (`L(ω, P)`), `CompactInduction.coefficientMap` (`E_P^G`),
  `CompactInduction.integrand`, `CompactInduction.coefficientMap_integral`,
  `CompactInduction.measure` (the Haar probability on `K`),
  `CompactInduction.formalDegreeProductForm` (the product of V.2) with
  `CompactInduction.formalDegreeProductForm_eq`, `product_inducingRepresentation`,
  `closedHalfCharacter_eq_comp_projection`, `IsUnimodularModulus`,
  `isUnitarizable_of_isSquareIntegrableModCentralSubgroup` and `representationFormalDegree`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermInd`: the induced constant term
  `constantTermInd` (`f^{(P),Ind}`), `IsConjModulus` and `IsConjModulus.constantTermInd_mul`,
  `IsBiInvariant.constantTermInd_mul`, and through its imports `Space.constantTerm`,
  `ConstantTermData` and `ConstantTermEstimate` (III.6);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.IwasawaIntegration`:
  `lintegral_eq_lintegral_levi_unipotent`, the integration formula
  `∫_G F = ∫_K ∫_M ∫_U F(m u k)` for nonnegative measurable `F`;
- `Langlands.Representation.Plancherel.CompactProductIntegralFormula` (Worker 200):
  `CompactInduction.productForm_inner_integral_integral` and
  `CompactInduction.integrable_productForm_pairing`, the product on `L(ω, P)` as an integral
  over `K × K`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- VII.1, printed p. 315 (PDF p. 81): "Pour `f ∈ C(G)`, on a défini `f^{(P)} ∈ C(M)` en III.6.
  On peut donc définir `f̂^{(P)}(ω, M) ∈ L^M(ω, M) = E ⊗ Ě`. On déduit de cette construction un
  élément noté `f̂^{(P),Ind}(ω) ∈ Ind_{P×P}^{G×G}(E ⊗ Ě) = L(ω, P)`, défini par
  `f̂^{(P),Ind}(ω)(g₁, g₂) = [f^{(P),Ind}(g₁, g₂)]^(ω, M)` pour tous `g₁, g₂ ∈ G`."
- Lemma VII.1.2, printed p. 315 (PDF p. 81): "Pour tout `f ∈ C(G)`, on a l'égalité
  `f̂(ω, P) = f̂^{(P),Ind}(ω)`."
- Proof of Lemma VII.1.2, printed pp. 315–316 (PDF pp. 81–82). By Lemma VII.1.1 (ii),
  `(v ⊗ v̌, f̂(ω, P)) = (E_P^G(v ⊗ v̌), f)_G = ∫_G conj(⟨π(g)v, v̌⟩) f(g) dg
  = ∫_G ∫_{P\G} conj(⟨v(hg), v̌(h)⟩) f(g) dh dg` (the overbars, checked on the page image, are
  written `conj`). Then: "Il résulte de la preuve du Lemme VI.2.2 et du Lemme II.1.5 que cette
  dernière intégrale est absolument convergente. On permute les intégrales". The proof writes
  `g = u m g'` with `δ_P(m)^{-1} du dm`, uses
  `⟨v(umg), v̌(h)⟩ = δ_P(m)^{1/2} E_M^M(v(g) ⊗ v̌(h))(m)` and
  `∫_U f(h⁻¹umg) du = δ_P(m)^{1/2} f^{(P),Ind}(g, h)(m)`, applies Lemma VII.1.1 (ii) for `M`, and
  recognizes the product of `L(ω, P)`.
- III.6 (printed pp. 271–272): `f^{(P)}(m) = δ_P(m)^{1/2} ∫_U f(m u) du` and
  `f^{(P),Ind}(g₁, g₂) = (ρ(g₁)λ(g₂)f)^{(P)}`.
- I.1, printed p. 240 (PDF p. 6): each closed subgroup `H` carries the left invariant measure
  with `mes(H ∩ K) = 1`; `G = PK`; and formula (2):
  `∫_G f(g) dg = ∫_{U×M×K} f(umk) δ_P(m)^{-1} dk dm du`.

The definition and Lemma VII.1.2 are source content. The Lean proof follows the source proof,
with these changes:

- the integral over `P\G` is the integral over `K` with its Haar probability, as in Worker 200's
  `CompactInduction.coefficientMap`;
- formula (2) is used in the coordinates `g = m u k`, as
  `∫_G F(g) dg = ∫_K ∫_M ∫_U F(m u k) du dm dk`. This is (2) after the substitution
  `u ↦ m u m⁻¹`, which scales `du` by `δ_P(m)`. The Library proves it for nonnegative `F`
  (`lintegral_eq_lintegral_levi_unipotent`), and this module extends it to integrable `F`. In
  these coordinates no modulus factor appears; the factor `δ_P(m)^{1/2}` of the induced vector
  combines with the integral over `U` into `f^{(P),Ind}(k, l)(m)`.

The Iwasawa section, `lift_smoothDualPairing_flip_eq`,
`inducingRepresentation_productLeviObject_apply`, `closedHalfCharacter_eq_sqrt`,
`lift_eval_levi_mul`, the `Space.constantTermInd` lemmas, `Space.exists_isBiInvariant`,
`integral_conj_lift_eval_mul` and the covariance and smoothness lemmas for the definition are
derived. `eval_inducedFourierTransform` is the pointwise form of Lemma VII.1.2.

### Correspondence with the source

- `(ω, E)` is `A : SmoothRep ℂ M`, irreducible (`hi`) and square integrable modulo a normal
  central subgroup `C` of `M` for a Haar measure `μM` on `M/C` (`hsq`). Waldspurger's `E_2(M)`
  takes square integrability modulo `A_M`. `d(ω)` is
  `representationFormalDegree C hC μM hcof hsq hi`.
- `P = MU` is given by `h : IsSemidirectDecomposition P M U`, and `K` is a compact open subgroup
  with `G = PK` (`hPK`). `L(ω, P)` is `productInducedCoefficientObject h hU A`. Its elements are
  functions `ψ` on `G × G` with values in `E ⊗ Ě` (`Induction.eval … ψ (g₁, g₂)`).
- `C(G)` is `Space Ξ σ` and `C(M)` is `Space ΞM σM`. The constant term along `P` uses a measure
  `ν` on `U` and the character `δ = HaarModulus.closedRestrictCharacter U hU M …`, the modulus of
  the conjugation action of `M` on `U` (Waldspurger's `δ_P` on `M`).
  `Space.constantTermInd hD hE ht htM f (g₁, g₂) ∈ C(M)` is `f^{(P),Ind}(g₁, g₂)`.
- `φ ↦ φ̂(ω, M)` is `coefficientFourierTransform A hwM hA hTM hΞM hσM d`, with
  `L^M(ω, M) = E ⊗ Ě` the coefficient tensor `CoefficientTensor A` and `d = d(ω)`.
- `E_M^M` is `coefficientTensorMap A` (`v ⊗ v̌ ↦ (m ↦ ⟨ω(m)v, v̌⟩)`). The pairing `⟨ , ⟩` on
  `E ⊗ Ě` is `TensorProduct.lift (smoothDualPairing A.representation).flip`.
- `(φ₁, φ₂)_X` is `∫ x, conj (φ₁ x) * φ₂ x`, antilinear in the first variable, as in the source.
  The product of V.2 on `L(ω, P)` is `CompactInduction.formalDegreeProductForm … hsq hi`.

## Scope and hypotheses

### Iwasawa section

`G` is a topological group with `SecondCountableTopology`, `MeasurableSpace` and `BorelSpace`.
`M`, `U` are subgroups with `[SecondCountableTopology U]` and `hMU : M ≤ normalizer U`. `μ`,
`μM`, `μU` are s-finite left invariant measures on `G`, `M`, `U`. `K` is a subgroup with
`hK : MeasurableSet K`. The hypotheses are:

- `hfac : ∀ g, ∃ m u, ∃ k ∈ K, g = m u k`;
- `hPK : ∀ m u, m u ∈ K ↔ m ∈ K ∧ u ∈ K`;
- `hMK : μM (M ∩ K) = 1` and `hUK : μU (U ∩ K) = 1`;
- `κ` an s-finite measure on `K` with `hκ : κ.map Subtype.val = μ.restrict K`.

These are the hypotheses of `lintegral_eq_lintegral_levi_unipotent`, plus `κ` and `hκ`.
`compactLeviUnipotentMul` and `compactLeviUnipotentMul_apply` use only the group structure.
`measurable_compactLeviUnipotentMul` uses the instances on `G` and no hypotheses.
`map_compactLeviUnipotentMul` and `integrable_comp_compactLeviUnipotentMul_iff` take all of the
above except `[SFinite κ]`; `integral_eq_integral_compact_levi_unipotent` takes all of them.

### Pairing section

`H` is a topological group and `B : SmoothRep ℂ H`; no further hypotheses.

### Inducing section

`G` is a locally compact, second countable, nonarchimedean topological group. `P`, `M`, `U` are
subgroups with `h : IsSemidirectDecomposition P M U`, `hU : IsClosed U` and `A : SmoothRep ℂ M`.
`closedHalfCharacter_eq_sqrt` and `lift_eval_levi_mul` also take
`hδU : IsUnimodularModulus U hU` (`U` unimodular). `closedHalfCharacter_eq_sqrt` does not use
second countability.

### Constant-term section

`G` is a topological group with `MeasurableSpace`, `BorelSpace` and
`Nonempty (CompactOpenSubgroup G)`. `M`, `U` are subgroups, `ν` is a measure on `U`,
`δ : M →* ℝ≥0ˣ`, and `Ξ σ : G → ℝ`, `ΞM σM : M → ℝ`. The hypotheses are
`hD : ConstantTermData ν δ`, `hE : ConstantTermEstimate ν δ Ξ σ ΞM σM` (Proposition II.4.5 for
the opposite parabolic), `ht : TranslationWeights Ξ σ` and `htM : TranslationWeights ΞM σM`.
`Space.constantTermInd_mul` also takes a left and right invariant `ν` and
`hν : IsConjModulus hMU ν δ` (`ν(m S m⁻¹) = δ(m) ν(S)`). `Space.exists_isBiInvariant` takes
only `f`.

### Definition section

As in the Inducing section, with `G` also `MeasurableSpace`, `BorelSpace` and
`Nonempty (CompactOpenSubgroup G)`, and the following data and hypotheses:

- `hδU : IsUnimodularModulus U hU`;
- `[Nonempty (CompactOpenSubgroup M)]`; a left and right invariant measure `μL` on `M`;
  `ΞM σM : M → ℝ` with `hwM : L2Weights μL ΞM σM`; `hA : IsAdmissible A.representation`;
  `hTM : HasTemperedCoefficients ΞM σM A.representation` (tempered growth of the coefficients of
  `ω`); `hΞM : ∀ m, ΞM m⁻¹ = ΞM m`; `hσM : ∀ m, σM m⁻¹ = σM m`; `d : ℝ`;
- a left and right invariant measure `ν` on `U`; `Ξ σ : G → ℝ`;
- `hD : ConstantTermData ν δ`, `hν : IsConjModulus h.levi_le_normalizer ν δ` and
  `hE : ConstantTermEstimate ν δ Ξ σ ΞM σM`, for
  `δ = HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer`;
- `ht : TranslationWeights Ξ σ`, `htM : TranslationWeights ΞM σM`.

For a regular Haar measure `ν` on a locally compact `U`, `hν` is the Library's
`isConjModulus_restrictCharacter`, and for `U` also nonarchimedean and `M` closed, `hD` is
`constantTermData_restrictCharacter`. Both are stated for `restrictCharacter`, which equals
`closedRestrictCharacter` by `closedRestrictCharacter_eq`. This module does not perform that
instantiation. The smoothness lemma does not use `hδU`, `hν`, second countability or the
invariance of `ν`.

### Unipotent section

As in the Inducing section, with `G` also `MeasurableSpace`, `hδU : IsUnimodularModulus U hU`
and an arbitrary measure `ν` on `U`. The function `f : G → ℂ` is arbitrary; no integrability
is assumed.

### Main section

The hypotheses of the transform section of `InducedFourierTransform`: `G` locally compact,
nonarchimedean, second countable, Hausdorff, with `MeasurableSpace`, `BorelSpace` and
`Nonempty (CompactOpenSubgroup G)`; `[LocallyCompactSpace P]`; `h`, `hU`, `hP : IsClosed P`,
`hm : Continuous h.projection`; `K : OpenSubgroup G`, `hK : IsCompact K`, `hPK : G = PK`;
`hG` (`G` unimodular); `hδ` (the modular character of `P` is the modulus of its action on `U`);
`A`, `hcof : CompactOpenCofinal M`; `C`, `hC`, `μM`, `hsq`, `hi`; a left and right invariant
measure `μ` on `G`; `hw : L2Weights μ Ξ σ`; `hT : HasTemperedCoefficients Ξ σ (I_P^G A)`; `hΞ`,
`hσ` (inversion symmetry of `Ξ`, `σ`). In addition, the data and hypotheses of the Definition
section except `hA` and `d`, which are `hsq.1` and `d(ω)`.

`inducedFourierTransform_eq_constantTermInducedFourierTransform` and
`eval_inducedFourierTransform` also take:

- `[MeasurableInv G]`, `[μ.IsInvInvariant]`, `[SigmaFinite μ]` and `hμK : μ K = 1`;
- `[MeasurableInv M]`, `[μL.IsInvInvariant]`, `[SFinite μL]` and `[SFinite ν]`;
- `hPKiw : ∀ (m : M) (u : U), m u ∈ K ↔ m ∈ K ∧ u ∈ K` (`P ∩ K = (M ∩ K)(U ∩ K)`);
- `hMK : μL (M ∩ K) = 1` and `hUK : ν (U ∩ K) = 1` (with `hμK`, the normalization
  `mes(H ∩ K) = 1` of I.1);
- `f : Space Ξ σ`;
- `hint`: for every `ψ ∈ L(ω, P)`, the function
  `(g, k) ↦ conj(CompactInduction.integrand h hU A K g ψ k) * f(g)` is integrable on `G × K` for
  `μ × CompactInduction.measure K hK`. Here
  `CompactInduction.integrand h hU A K g ψ k = ⟨ψ(k g, k)⟩`. This is the absolute convergence of
  `∫_G ∫_{P\G} conj(⟨v(hg), v̌(h)⟩) f(g) dh dg` that the source deduces from the proof of Lemma
  VI.2.2 and from Lemma II.1.5.

`eval_inducedFourierTransform` also takes `x : G × G`.

## Definitions

- `compactLeviUnipotentMul : K × (M × U) → G`, `(k, (m, u)) ↦ m u k`.
- `Space.constantTermInd hD hE ht htM f g : Space ΞM σM` is
  `Space.constantTerm … (Space.translate ht g.1 g.2 f)`, i.e. `f^{(P),Ind}(g₁, g₂)` in `C(M)`.
- `constantTermInducedFourierTransform h hU hδU A hwM hA hTM hΞM hσM d hD hν hE ht htM f :
  productInducedCoefficientObject h hU A` is `f̂^{(P),Ind}(ω)`. It is the induced function
  `x ↦ coefficientFourierTransform A hwM hA hTM hΞM hσM d (Space.constantTermInd … f x)`, built
  with `Induction.smoothFunctionOf`. Its covariance under `P × P` is
  `constantTermInducedFourierTransform_covariant`. It is right invariant under `H × H` for a
  compact open subgroup `H` under which `f` is bi-invariant, chosen by `Classical.choose` from
  `Space.exists_isBiInvariant`. For `d = d(ω)` this is Waldspurger's `f̂^{(P),Ind}(ω)`.

## Results

### Iwasawa section

- `compactLeviUnipotentMul_apply` (definitional) and `measurable_compactLeviUnipotentMul`.
- `map_compactLeviUnipotentMul`: `(κ × (μM × μU)).map compactLeviUnipotentMul = μ`.
- `integrable_comp_compactLeviUnipotentMul_iff`: for `F` a.e. strongly measurable,
  `F ∘ compactLeviUnipotentMul` is integrable for `κ × (μM × μU)` iff `F` is integrable for `μ`.
- `integral_eq_integral_compact_levi_unipotent`: for integrable `F` with values in a real Banach
  space, `∫ g, F g ∂μ = ∫ k, ∫ m, ∫ u, F (m u k) ∂μU ∂μM ∂κ`.

### Pairing and inducing sections

- `lift_smoothDualPairing_flip_eq`: the pairing `v ⊗ ℓ ↦ ℓ(v)` of `t ∈ B ⊗ B̃` equals
  `coefficientTensorMap B t 1`.
- `inducingRepresentation_productLeviObject_apply`: the inducing representation of `L(ω, P)` at
  `p = (p₁, p₂) ∈ P × P` acts on `E ⊗ Ě` by
  `δ_P(p₁)^{1/2} δ_P(p₂)^{1/2} (ω(m(p₁)) ⊗ ω̌(m(p₂)))`, where `δ_P^{1/2}` is
  `HaarModulus.closedHalfCharacter U hU P …` and `m = h.projection`.
- `closedHalfCharacter_eq_sqrt`: with `U` unimodular, `δ_P(q)^{1/2}` is the square root of
  `δ(m(q))` for `δ = closedRestrictCharacter U hU M …`.
- `lift_eval_levi_mul`: for `ψ ∈ L(ω, P)`,
  `⟨ψ(m u k, l)⟩ = δ(m)^{1/2} E_M^M(ψ(k, l))(m)`. This is the identity
  `⟨v(umg), v̌(h)⟩ = δ_P(m)^{1/2} E_M^M(v(g) ⊗ v̌(h))(m)` of the source proof, in the order
  `m u`.

### Constant-term section

- `Space.coe_constantTermInd` (definitional): the function underlying
  `Space.constantTermInd … f g` is `constantTermInd ν δ f g`.
- `Space.exists_isBiInvariant`: every `f ∈ C(G)` is bi-invariant under some compact open
  subgroup.
- `Space.constantTermInd_mul`: `f^{(P),Ind}(m₁ u₁ g₁, m₂ u₂ g₂) =
  δ(m₁)^{1/2} δ(m₂)^{1/2} ρ(m₁)λ(m₂) f^{(P),Ind}(g₁, g₂)` in `C(M)`; this is
  `IsConjModulus.constantTermInd_mul` on `C(M)`.

### Definition section

- `constantTermInducedFourierTransform_covariant`: for `p ∈ P × P` and `x ∈ G × G`, the value at
  `p x` is the inducing representation of `p` applied to the value at `x`.
- `constantTermInducedFourierTransform_mul_right`: right invariance under `H × H` when `f` is
  bi-invariant under `H`.
- `eval_constantTermInducedFourierTransform` (definitional):
  `f̂^{(P),Ind}(ω)(g₁, g₂) = [f^{(P),Ind}(g₁, g₂)]^(ω, M)`.

### Unipotent and main sections

- `integral_conj_lift_eval_mul`: for `ψ ∈ L(ω, P)`, `f : G → ℂ`, `k, l ∈ G` and `m ∈ M`,
  `∫_U conj(⟨ψ(m u k, l)⟩) f(l⁻¹ m u k) dν(u) =
  conj(E_M^M(ψ(k, l))(m)) f^{(P),Ind}(k, l)(m)`.
- `inducedFourierTransform_eq_constantTermInducedFourierTransform` (**Lemma VII.1.2**):
  `inducedFourierTransform … f = constantTermInducedFourierTransform … d(ω) … f`, that is
  `f̂(ω, P) = f̂^{(P),Ind}(ω)`.
- `eval_inducedFourierTransform`: `f̂(ω, P)(g₁, g₂) = [f^{(P),Ind}(g₁, g₂)]^(ω, M)`.

## Proof notes

1. `map_compactLeviUnipotentMul`: test against nonnegative measurable `F`. Pull back along the
   map, apply Tonelli on `κ × (μM × μU)`, and push `κ` forward to `μ.restrict K` by `hκ`. Then
   use `lintegral_eq_lintegral_levi_unipotent`. Integrability and the Bochner formula follow
   from the image-measure identity and Fubini.
2. `inducingRepresentation_productLeviObject_apply`: rewrite with Worker 200's
   `product_inducingRepresentation` and compute `TensorProduct.map (c₁ • a) (c₂ • b)` with
   `map_smul_left`, `map_smul_right`.
3. `lift_eval_levi_mul`: write `(m u k, l) = (m u, 1)(k, l)` with `(m u, 1) ∈ P × P`, use the
   covariance of `ψ` and step 2. The projection of `m u` is `m` and that of `1` is `1`; by
   `closedHalfCharacter_eq_comp_projection` (`U` unimodular) the half modulus of `m u` is
   `δ(m)^{1/2}`. Finally the pairing of `(ω(m) ⊗ 1) t` is `coefficientTensorMap A t m`
   (`lift_smoothDualPairing_flip_eq`, `coefficientTensorMap_action`).
4. Covariance of the definition: for `p = (p₁, p₂)` write `pᵢ = m(pᵢ) uᵢ`. Apply
   `Space.constantTermInd_mul`, `map_smul`, and `coefficientFourierTransform_translate` for `M`
   (Lemma VII.1.1 (i) for `M`), then compare with steps 2 and 3. Smoothness follows from
   `IsBiInvariant.constantTermInd_mul`.
5. `integral_conj_lift_eval_mul`: by step 3 the integrand is
   `conj(E_M^M(ψ(k, l))(m)) δ(m)^{1/2} f(l⁻¹ (m u) k)`. Pull the constants out of the integral;
   what remains is `constantTermInd ν δ f (k, l) m = δ(m)^{1/2} ∫_U f(l⁻¹ m u k) du`.
6. Lemma VII.1.2: by `inducedFourierTransform_eq_of_forall_integral` it suffices to show
   `(E_P^G ψ, f)_G = (ψ, f̂^{(P),Ind}(ω))` for all `ψ ∈ L(ω, P)`. Choose a positive invariant form
   `b` on `A`. By `formalDegreeProductForm_eq` and `productForm_inner_integral_integral`, the
   right side is `d(ω)⁻¹ ∫_K ∫_K B(ψ(k, l), f̂^{(P),Ind}(ω)(k, l)) dl dk`, for `B` the
   coefficient-tensor form of `b`. On the left, `E_P^G ψ(g) = ∫_K ⟨ψ(l g, l)⟩ dl`
   (`coefficientMap_integral`). Exchange the integrals over `G` and `K` (Fubini, `hint`). For
   almost every `l`, substitute `g ↦ l g` (left invariance of `μ`). Apply
   `integral_eq_integral_compact_levi_unipotent`, with the needed integrability from `hint` and
   left invariance, and `κ = CompactInduction.measure K hK`. Here `hκ` holds because the
   normalized Haar measure with `mes(K) = 1` is `μ` (`haarMeasure_unique`, `hμK`). Then step 5,
   and Lemma VII.1.1 (ii) for `M` (`integral_conj_coefficientTensorMap_mul_eq_inner` with
   `d = d(ω)`), turn the inner integral over `M × U` into `d(ω)⁻¹ B(ψ(k, l),
   f̂^{(P),Ind}(ω)(k, l))`. A last exchange of the two integrals over `K` uses
   `integrable_productForm_pairing`.
7. `eval_inducedFourierTransform`: rewrite with Lemma VII.1.2 and evaluate the definition.

## Relation to the Library

- `InducedFourierTransform` defines `f̂(ω, P)` and proves Lemma VII.1.1. This module identifies
  `f̂(ω, P)` with the transform of the constant term (Lemma VII.1.2), the reduction that
  Waldspurger uses in Proposition VII.1.3 and later to pass from `G` to `M`.
- `ConstantTermInd` proves the `P × P` law of `f^{(P),Ind}` for functions. This module lifts it
  to `C(M)` and through the Fourier transform of `C(M)` to `L(ω, P)`.
- The Iwasawa section is the Bochner-integral form of `lintegral_eq_lintegral_levi_unipotent`.

## Open obligations

- The absolute convergence `hint` (from the proof of Lemma VI.2.2 and Lemma II.1.5) is a
  hypothesis and is not proved here.
- Instantiating `hE` (Proposition II.4.5), `hwM`, `hTM` and the weights for Waldspurger's
  `Ξ^M`, `σ^M`, and `hν`, `hD` for a Haar measure on `U`, is not done here.
- Proposition VII.1.3 and Lemma VII.1.4 are not addressed.
