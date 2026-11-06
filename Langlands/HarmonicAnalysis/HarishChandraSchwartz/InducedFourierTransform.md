# The Fourier transform on `L(ω, P)` (Waldspurger VII.1, Lemma VII.1.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierTransform`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierTransform`: the generic transform
  `coefficientFourierTransform A hw hA hT hΞ hσ d` (`f ↦ d π(f̌)` in `A ⊗ Ã`) with
  `coefficientFourierTransform_translate`, `coefficientTensorMap_coefficientFourierTransform`
  and `integral_conj_coefficientTensorMap_mul_eq_inner` (the generic forms of Lemma VII.1.1
  (i)–(iii)), `schwartzCharacter` (`θ_π`), `Space`, `Space.check` (`f ↦ f̌`), `Space.translate`
  (`ρ(g₁) λ(g₂)`), `L2Weights`, `TranslationWeights` and `HasTemperedCoefficients`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientXi`:
  `norm_coefficientMap_le_xi` (Lemma VI.2.2 for one induced representation) and, through its
  imports, Worker 200's `productInducedCoefficientObject` (`L(ω, P)`),
  `CompactInduction.coefficientTensorEquiv`, `CompactInduction.coefficientMap` (`E_P^G`),
  `CompactInduction.induced_isAdmissible`, `coefficientTensorMap`, `coefficientTensorAction`,
  `xi`, `LeviData`, `IsIwasawaPair` and `IsUnimodularModulus`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity`:
  `isUnitarizable_of_isSquareIntegrableModCentralSubgroup`, `representationFormalDegree` and
  `representationFormalDegree_pos`;
- `Langlands.Representation.Plancherel.CompactProductInducedForm` (Worker 200): the product of
  V.2 on `L(ω, P)`, `CompactInduction.formalDegreeProductForm`, with
  `CompactInduction.formalDegreeProductForm_eq_coefficientForm` and
  `CompactInduction.invariantPositiveForm`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- VII.1, printed p. 313 (PDF p. 79): "Soient `P = MU` un sous-groupe parabolique semi-standard
  de `G` et `(ω, E) ∈ E_2(M)`. On définit une application `C(G) → L(ω, P)`, `f ↦ f̂(ω, P)` de la
  façon suivante. Posons `π = I_P^G ω`. Notons `f̌` la fonction sur `G` définie par
  `f̌(g) = f(g⁻¹)`. On a `f̌ ∈ C(G)`, on peut donc définir `π(f̌) ∈ End(I_P^G E)`, cf. III.7.
  D'autre part, on a un plongement `L(ω, P) = (I_P^G E) ⊗ (I_P^G E)ˇ ↪ End(I_P^G E)`. (1)
  Comme `f̌` est bi-invariante par un sous-groupe ouvert compact de `G`, `π(f̌)` appartient à
  l'image de cette application et s'identifie donc à un élément de `L(ω, P)`. Alors `f̂(ω, P)`
  est le produit de cet élément par `d(ω)`." Then: "Notons `θ^G_ω` le caractère de `π` … si
  `f₁`, `f₂` sont deux fonctions sur `X` telles que `f̄₁ f₂ ∈ L¹(X)`, posons
  `(f₁, f₂)_X = ∫_X f̄₁(x) f₂(x) dx`."
- Lemma VII.1.1, printed p. 314 (PDF p. 80): "Soient `f ∈ C(G)`, `g, h ∈ G` et `ψ ∈ L(ω, P)`.
  On a les égalités (i) `(ρ(g)λ(h)f)^(ω, P) = (π(g) ⊗ π̌(h))(f̂(ω, P))`; (ii)
  `(E_P^G ψ, f)_G = (ψ, f̂(ω, P))`; (iii) `(E_P^G f̂(ω, P))(g) = d(ω) θ^G_ω(λ(g) f̌)`." The proof
  of (ii) writes `(E_P^G ψ, f)_G = ∫_G conj(⟨π(g)v, v̌⟩) f(g) dg` for `ψ = v ⊗ v̌` (the overbar,
  checked on the page image, is written `conj`).
- The product on `L(ω, P)`, V.2, printed p. 293 (PDF p. 59):
  `(v₁ ⊗ v̌₁, v₂ ⊗ v̌₂) = d(ω)⁻¹ (v₁, v₂)(v̌₁, v̌₂)` for the products on `I_P^G E` and
  `I_P^G Ě` deduced from a positive definite invariant product on `E`; it does not depend on that
  product. `L(ω, P) = I_{P×P}^{G×G}(E ⊗ Ě)` and `E_P^G (v ⊗ v̌)(g) = ⟨π(g)v, v̌⟩`, V.1, printed
  p. 288 (PDF p. 54).
- Lemma VI.2.2, printed p. 298 (PDF p. 64), and Corollary III.1.2 for `M` are the source of the
  tempered growth used in `hasTemperedCoefficients_normalizedInduction`.

The definition and parts (i)–(iii) are source content. The construction is derived as follows: it
is the generic transform `coefficientFourierTransform` of `FourierTransform` for the normalized
induced representation `I_P^G E` with `d = d(ω)`, carried to `L(ω, P)` by the inverse of
Worker 200's identification `CompactInduction.coefficientTensorEquiv` of `L(ω, P)` with
`I_P^G E ⊗ (I_P^G E)~`. This is the identification `L(ω, P) = (I_P^G E) ⊗ (I_P^G E)ˇ` in VII.1
(1). The imported `CompactInduction.induced_isAdmissible`,
`coefficientTensorEquiv_inducedFourierTransform`, the
uniqueness statement `inducedFourierTransform_eq_of_forall_integral` and
`hasTemperedCoefficients_normalizedInduction` are derived. The uniqueness follows from (ii) and
the definiteness of the V.2 product. The tempered-growth statement follows from Lemma VI.2.2.

### Correspondence with the source

- `(ω, E)` is `A : SmoothRep ℂ M`, irreducible (`hi`) and square integrable modulo a normal
  central subgroup `C` of `M` for a Haar measure `μM` on `M/C` (`hsq`). Waldspurger's `E_2(M)`
  takes square integrability modulo `A_M`. Here `C` is any normal subgroup of the centre.
  `d(ω)` is `representationFormalDegree C hC μM hcof hsq hi`, the formal degree for `μM`.
- `P = MU` is a subgroup `P` with `h : IsSemidirectDecomposition P M U`; `K` is a compact open
  subgroup with `G = P K`. `π = I_P^G ω` is `(normalizedInductionFunctor h hU).obj A`.
- `C(G)` is `Space Ξ σ` for weights `Ξ`, `σ` satisfying `hw : L2Weights μ Ξ σ`: positivity of
  `Ξ`, nonnegativity of `σ`, and `∫_G Ξ² (1 + σ)^{-d} dμ < ∞` for some `d` (Lemma II.1.5 for
  Waldspurger's `Ξ`, `σ`). `μ` is the measure `dg` on `G`.
- `π(f̌)` is the generic Schwartz action of `FourierTransform` (`π(φ) = ∫_G φ(g) π(g) dg` for
  `φ ∈ C(G)`, Waldspurger III.7), which needs the coefficients of `π` to have tempered growth:
  the hypothesis `hT : HasTemperedCoefficients Ξ σ π`, i.e. for all `v`, `ℓ` there are `c`, `r`
  with `|ℓ(π(g) v)| ≤ c Ξ(g) (1 + σ(g))^r`. Waldspurger defines `π(f)` for tempered `π` in III.7.
  For his `Ξ`, `hasTemperedCoefficients_normalizedInduction` supplies `hT` from Corollary
  III.1.2 for `M`.
- `L(ω, P)` is `productInducedCoefficientObject h hU A`, with `G × G` acting by its
  representation. `E_P^G` is `CompactInduction.coefficientMap … hsq.1`. This is
  `E_P^G (v ⊗ v̌)(g) = ⟨π(g)v, v̌⟩` with `⟨v, v̌⟩ = ∫_K ⟨v(k), v̌(k)⟩ dk` for the Haar
  probability on `K`. This matches Waldspurger's normalization `mes(K) = 1` (I.1, printed
  p. 240).
- The product of V.2 on `L(ω, P)` is `CompactInduction.formalDegreeProductForm … hsq hi`. It is
  antilinear in its first variable, as is Waldspurger's. `(φ₁, φ₂)_G` is
  `∫ g, conj (φ₁ g) * φ₂ g ∂μ`.
- `ρ(g₁) λ(g₂) f` is `Space.translate ht g₁ g₂ f`, `x ↦ f(g₂⁻¹ x g₁)`, and `π(g₁) ⊗ π̌(g₂)` is
  the action of `(g₁, g₂)` on `L(ω, P)`. `θ^G_ω(φ)` is `schwartzCharacter hw … hT φ`, the trace
  of `π(φ)`.

## Scope and hypotheses

### Transform section

Instances on `G`: `Group`, `TopologicalSpace`, `LocallyCompactSpace`, `NonarchimedeanGroup`,
`SecondCountableTopology`, `T2Space`, `MeasurableSpace`, `BorelSpace`, and
`Nonempty (CompactOpenSubgroup G)`. Subgroups `P`, `M`, `U` of `G` with
`[LocallyCompactSpace P]`. Explicit data and hypotheses, all taken by the definition and the
theorems unless stated otherwise:

- `h : IsSemidirectDecomposition P M U`, `hU : IsClosed U`, `hP : IsClosed P`,
  `hm : Continuous h.projection`;
- `K : OpenSubgroup G`, `hK : IsCompact K`, `hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q * k`;
- `hG : ∀ g, Measure.modularCharacter g = 1` (`G` unimodular);
- `hδ : ∀ q : P, Measure.modularCharacter q = HaarModulus.closedRestrictCharacter U hU P … q`
  (the modular character of `P` is the modulus of its conjugation action on `U`);
- `A : SmoothRep ℂ M`, `hcof : CompactOpenCofinal M`;
- `C` a normal subgroup of `M` with `hC : C ≤ Subgroup.center M`, a measurable structure with
  `BorelSpace` on `M/C`, and `μM` a Haar measure on `M/C` that is inversion invariant;
- `hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM` (this includes
  admissibility, `hsq.1`), `hi : A.representation.IsIrreducible`;
- `μ` a measure on `G` that is left and right invariant; `Ξ σ : G → ℝ` with
  `hw : L2Weights μ Ξ σ`, `hT : HasTemperedCoefficients Ξ σ π` for `π = I_P^G A`,
  `hΞ : ∀ g, Ξ g⁻¹ = Ξ g` and `hσ : ∀ g, σ g⁻¹ = σ g`.

Further hypotheses:

- The imported `CompactInduction.induced_isAdmissible h hU K hK hPK A hm hA` takes only `h`, `hU`, `hm`, `K`, `hK`,
  `hPK`, `A`, `hA : A.IsAdmissible` and the instances `Group`, `TopologicalSpace`,
  `LocallyCompactSpace`, `NonarchimedeanGroup` on `G`.
- `inducedFourierTransform_translate` and `coefficientMap_inducedFourierTransform` also take
  `ht : TranslationWeights Ξ σ`.
- `integral_conj_coefficientMap_mul_eq_inner` and `inducedFourierTransform_eq_of_forall_integral`
  also take `[MeasurableInv G]` and `[μ.IsInvInvariant]`. The uniqueness theorem takes `φ ∈ L(ω, P)`
  and `hφ : ∀ ψ, (E_P^G ψ, f)_G = (ψ, φ)`.

### Tempered section

Instances on `G`: `Group`, `TopologicalSpace`, `LocallyCompactSpace`, `NonarchimedeanGroup`,
`SecondCountableTopology`, `T2Space`, `MeasurableSpace`, `BorelSpace`. Subgroups `P`, `M`, `U`
with `[LocallyCompactSpace P]`. A subgroup `P₀` with characters `δ₀ : P₀ →* ℝ≥0ˣ` and
`δ₀M : P₀ ∩ M →* ℝ≥0ˣ`, and instances `[CompactSpace K]`, `[CompactSpace (K ∩ M)]`.
`hasTemperedCoefficients_normalizedInduction` takes exactly the hypotheses of
`norm_coefficientMap_le_xi` (with the inducing representation `A` arbitrary):

- `h`, `hU`, `A`, `K`, `hK`, `hP`, `hm`, `hPK`, `hG`, and `hδP` (the hypothesis `hδ` of the
  transform section);
- `hA : A.IsAdmissible`;
- `hδ : IsUnimodularModulus U hU` (`U` unimodular);
- `hL : LeviData K P₀ P M δ₀ δ_P δ₀M h.projection` with
  `δ_P = HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer`;
- `hP₀K : IsIwasawaPair P₀ K` (`G = P₀ K`) and `hMK : IsIwasawaPair (P₀ ∩ M) (K ∩ M)`;
- `hδ₀ : ∀ p : P₀, p ∈ K → δ₀ p = 1`;
- `hcoeff` (Corollary III.1.2 for `M`): for all `v ∈ A` and smooth dual vectors `ℓ` there is
  `C > 0` with `‖ℓ(A(m) v)‖ ≤ C Ξ^M(m)` for all `m ∈ M`, where `Ξ^M = xi hMK δ₀M`;
- `σ : G → ℝ` arbitrary.

Using its conclusion as `hT` with `Ξ = xi hP₀K δ₀` requires `hw : L2Weights μ Ξ σ` for that
`Ξ` (Lemma II.1.5), which this module does not supply.

## Definitions

- `inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ :
  Space Ξ σ →ₗ[ℂ] productInducedCoefficientObject h hU A` is `f ↦ f̂(ω, P)`, the inverse of
  `CompactInduction.coefficientTensorEquiv` applied to
  `coefficientFourierTransform (I_P^G A) … d(ω) f = d(ω) π(f̌)`.

## Results

- The imported `CompactInduction.induced_isAdmissible` supplies
  `IsAdmissible (I_P^G A).representation` for admissible `A`; the representation
  and smooth-representation admissibility predicates are definitionally equal.
- `coefficientTensorEquiv_inducedFourierTransform`: `coefficientTensorEquiv (f̂(ω, P))` is
  `coefficientFourierTransform (I_P^G A) … d(ω) f`, i.e. `d(ω) π(f̌)` under VII.1 (1).
- `inducedFourierTransform_translate` (Lemma VII.1.1 (i)):
  `(ρ(g₁) λ(g₂) f)^(ω, P) = (π(g₁) ⊗ π̌(g₂)) f̂(ω, P)`, with the right side the action of
  `(g₁, g₂)` on `L(ω, P)`.
- `integral_conj_coefficientMap_mul_eq_inner` (Lemma VII.1.1 (ii)):
  `∫_G conj((E_P^G ψ)(g)) f(g) dμ(g) = (ψ, f̂(ω, P))` for the product of V.2.
- `coefficientMap_inducedFourierTransform` (Lemma VII.1.1 (iii)):
  `(E_P^G f̂(ω, P))(g) = d(ω) θ^G_ω(λ(g) f̌)`, where `λ(g) f̌` is `Space.translate ht 1 g (f̌)`.
- `inducedFourierTransform_eq_of_forall_integral`: if `φ ∈ L(ω, P)` satisfies
  `(E_P^G ψ, f)_G = (ψ, φ)` for every `ψ ∈ L(ω, P)`, then `φ = f̂(ω, P)`.
- `hasTemperedCoefficients_normalizedInduction`: under Corollary III.1.2 for `M`, every
  coefficient of `I_P^G A` is bounded by `c Ξ(g)` with `Ξ = xi hP₀K δ₀`. So `I_P^G A` has tempered
  coefficients for `Ξ` and every `σ`, with exponent `r = 0`.

## Proof notes

1. `coefficientTensorEquiv_inducedFourierTransform`: unfold the definition and cancel the
   equivalence with its inverse (`Representation.Equiv.apply_symm_apply`).
2. (i): rewrite with the generic `coefficientFourierTransform_translate`, then use that the
   inverse equivalence intertwines the `G × G` actions (`isIntertwining'` of
   `coefficientTensorEquiv.symm`).
3. (iii): `CompactInduction.coefficientMap` is `coefficientTensorMap` composed with
   `coefficientTensorEquiv`. Rewrite with step 1 and apply the generic
   `coefficientTensorMap_coefficientFourierTransform`.
4. (ii): choose a positive invariant form `b` on `A`
   (`isUnitarizable_of_isSquareIntegrableModCentralSubgroup`). By
   `formalDegreeProductForm_eq_coefficientForm` the V.2 product is the transport along
   `coefficientTensorEquiv` of `d(ω)⁻¹` times the coefficient-tensor form induced by the form
   that `b` induces on `I_P^G A`. Rewrite with step 1 and apply the generic
   `integral_conj_coefficientTensorMap_mul_eq_inner` with `d = d(ω) > 0`
   (`representationFormalDegree_pos`).
5. Uniqueness: by (ii) and `hφ`, `(ψ, f̂(ω, P)) = (ψ, φ)` for all `ψ`. Taking
   `ψ = f̂(ω, P) - φ` gives `(ψ, ψ) = 0`, and definiteness gives `f̂(ω, P) = φ`.
6. Tempered coefficients: for `v ∈ I_P^G A` and a smooth dual vector `ℓ`, the coefficient
   `g ↦ ℓ(π(g) v)` is `E_P^G` of the inverse image of `v ⊗ ℓ` under `coefficientTensorEquiv`
   (`coefficientTensorMap_tmul`). `norm_coefficientMap_le_xi` bounds it by `c Ξ(g)`, which is
   tempered growth with `r = 0`.

## Relation to the Library

- `FourierTransform` proves Lemma VII.1.1 for the coefficient tensor `A ⊗ Ã` of any admissible
  representation with tempered coefficients. This module specializes it to `π = I_P^G ω` on the
  source's space `L(ω, P)` with the V.2 product, and adds the tempered-growth input from Lemma
  VI.2.2.

## Open obligations

- Instantiating `hw` for Waldspurger's `Ξ` and `σ` (Lemma II.1.5) and `hcoeff` (Corollary III.1.2
  for `M`) is not done here.
- Lemmas VII.1.2–VII.1.4 and Proposition VII.1.3 for `L(ω, P)` are not addressed.
