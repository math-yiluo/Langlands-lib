# The Fourier transform `f ↦ f̂(ω, P)` for actual standard parabolic subgroups (Waldspurger VII.1)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedFourierTransform`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedCoefficients` (this author's
  Unit 19, candidate `181a067e-76c8-4bae-b922-0bd659adbf51`, accepted). It provides:
  - the coefficient map `rationalInducedCoefficientMap` (`E_P^G`);
  - the actual-point facts `isClosed_standardParabolicPoints_rootSet`,
    `locallyCompactSpace_standardParabolicPoints_rootSet` and
    `exists_standardParabolicPoints_rootSet_mul`;
  - the local instances on `G(F)` (`rationalInducedSecondCountable`, `rationalInducedT2`,
    `rationalInducedNonarchimedean`).

  Through it come the published Units 11–14:
  - `isSemidirectDecomposition_standard`, `continuous_projection_standard`;
  - `modularCharacter_standardParabolicPoints`;
  - `compactSpace_subgroupOf_standardLevi`;
  - `IsRationalLeviTempered` and `rationalHasTemperedCoefficients_normalizedInduction`
    (Lemma III.2.3);
  - `rationalXi`, `rationalHeight`, `rationalHeight_inv`, `rationalHeightSubgroup`,
    `RationalSchwartzSpace`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierTransform`: the abstract
  transform `inducedFourierTransform` and its lemmas:
  - `inducedFourierTransform_translate` (Lemma VII.1.1 (i));
  - `integral_conj_coefficientMap_mul_eq_inner` (VII.1.1 (ii));
  - `coefficientMap_inducedFourierTransform` (VII.1.1 (iii)).

  Through its imports come `CompactInduction.formalDegreeProductForm` (the product of V.2 on
  `L(ω, P)`, with `toInnerProductCore` and `definite`), `CompactInduction.induced_isAdmissible`,
  `representationFormalDegree`, `schwartzCharacter`, `Space.translate`, `Space.check`,
  `CompactOpenSubgroup.cofinal` and `productInducedCoefficientObject`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay` (Unit 15):
  `rationalTranslationWeights` (Lemma II.1.2). Through its imports (Unit 12) come
  `rationalL2Weights` and `rationalXi_inv` (Lemma II.1.4).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
text of PDF pages 79 and 80.

- VII.1, printed p. 313: "Soient `P = MU` un sous-groupe parabolique semi-standard de `G` et
  `(ω, E) ∈ E_2(M)`. On définit une application `C(G) → L(ω, P)`, `f ↦ f̂(ω, P)` de la façon
  suivante. Posons `π = I_P^G ω`. Notons `f̌` la fonction sur `G` définie par
  `f̌(g) = f(g⁻¹)`. [...] on a un plongement `L(ω, P) = (I_P^G E) ⊗ (I_P^G E)ˇ ↪ End(I_P^G E)`.
  (1) [...] `π(f̌)` appartient à l'image de cette application et s'identifie donc à un élément
  de `L(ω, P)`. Alors `f̂(ω, P)` est le produit de cet élément par `d(ω)`."
- Lemme VII.1.1, printed p. 314: "Soient `f ∈ C(G)`, `g, h ∈ G` et `ψ ∈ L(ω, P)`. On a les
  égalités (i) `(ρ(g)λ(h)f)^(ω, P) = (π(g) ⊗ π̌(h))(f̂(ω, P))`; (ii)
  `(E_P^G ψ, f)_G = (ψ, f̂(ω, P))`; (iii) `(E_P^G f̂(ω, P))(g) = d(ω) θ^G_ω(λ(g) f̌)`."

`InducedFourierTransform.md` explains how the abstract `inducedFourierTransform` and its lemmas
correspond to these definitions. It covers the identification (1), the product of V.2 on
`L(ω, P)`, `(f₁, f₂)_G = ∫_G conj(f₁) f₂`, and `θ^G_ω` as `schwartzCharacter`. This module adds
no new analysis: it supplies the actual data of a standard parabolic `P_I(F)` and checks the
abstract hypotheses on actual points.

## Setting

- `F` is a nonarchimedean local field.
- `G` is a group scheme over `Spec F` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`, and `hG : IsConnectedReductive G`.
- `i` is a maximal split torus (`hi`), `ν` a generic cocharacter (`hν`), and `I` a finite set of
  simple roots, with `P = P_I(F) = M_I(F) ⋉ U_I(F)`.
- `K` is an open subgroup of `G(F)`, with `hKc` (`K` is compact) and `hPK : IsIwasawaPair P₀(F) K`.
- `ρ : MatrixRepresentation G (Fin N)` defines `σ = rationalHeight ρ`. It is closed (`hρ`) and
  `ρ(K) ⊆ GL_N(𝒪)` (`hKρ : K ≤ rationalHeightSubgroup ρ`). `C(G)` is
  `RationalSchwartzSpace hKc hPK ρ`, the Library's `Space Ξ σ` for `Ξ = rationalXi hKc hPK`.
- `hM : IsIwasawaPair (P₀(F) ∩ M_I(F)) (K ∩ M_I(F))`, which defines `Ξ^{M_I}`.
- `M_I(F)` is written as the subtype `𝐌` of `rationalPoints G`, as in Units 20 and 21.
- `ω = A` is a smooth representation of `M_I(F)` with the following data:
  - a normal subgroup `C ≤ center M_I(F)` (`hC`);
  - a Haar measure `μM` on `M_I(F)/C`, inverse-invariant;
  - `hsq`: `A` is square integrable modulo `C`, which includes admissibility (`hsq.1`);
  - `hirr`: `A` is irreducible;
  - `hTA : IsRationalLeviTempered hKc ρ hM A`: the coefficients of `A` have tempered growth for
    `Ξ^{M_I}` and `σ`.

  Waldspurger takes `(ω, E) ∈ E_2(M)` and `C = A_M(F)`. For such `ω` the temperedness is a
  consequence of Corollary III.1.2, whose actual statement
  `RationalSquareIntegrableRapidDecayStatement` is published but not proved.
- `mu` is a left and right invariant measure on `G(F)`, for example a Haar measure on the
  unimodular group `G(F)`.
- `hsw : SquareIntegrableWeight mu Ξ σ` is the conclusion of Lemma II.1.5: `∫ Ξ² (1 + σ)^{-d}`
  is finite for some `d`. The actual statement `RationalXiSquareIntegrableStatement` (Unit 12)
  gives it under the structural hypotheses recorded there; it is not proved.

## Contents

- `compactOpenCofinal_standardLevi I hKc`: compact open subgroups are cofinal in `M_I(F)`.
  `K ∩ M_I(F)` is a compact open subgroup of `M_I(F)` (`compactSpace_subgroupOf_standardLevi`),
  so the Library's `CompactOpenSubgroup.cofinal` applies. Formal degrees on `M_I(F)` need this
  (`representationFormalDegree`).
- **`rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq hirr hTA hsw`**
  (definition, the recorded declaration). It is the ℂ-linear map `C(G) → L(ω, P)`,
  `f ↦ f̂(ω, P) = d(ω) π(f̌)`: the Library's `inducedFourierTransform`, with these inputs:
  - the actual decomposition `isSemidirectDecomposition_standard` and the closedness of
    `U_I(F)` and `P_I(F)`;
  - `G(F) = P_I(F) K`;
  - the unimodularity of `G(F)` (`rationalReductiveUnimodularity` with `standardCocharacter`)
    and the modular character of `P_I(F)`;
  - the cofinality above;
  - `L2Weights` from `hsw` (`rationalL2Weights`);
  - the tempered growth of `I_P^G A` (`rationalHasTemperedCoefficients_normalizedInduction`,
    Lemma III.2.3, from `hTA`);
  - `Ξ(g⁻¹) = Ξ(g)` (`rationalXi_inv`, Lemma II.1.4) and `σ(g⁻¹) = σ(g)` (`rationalHeight_inv`).
- **`rationalInducedFourierTransform_translate g₁ g₂ f`** (Lemma VII.1.1 (i)):
  `(ρ(g₁) λ(g₂) f)^(ω, P) = (π(g₁) ⊗ π̌(g₂)) f̂(ω, P)`. Here `ρ(g₁) λ(g₂)` is the two-sided
  translation `Space.translate` of `C(G)` for the actual `TranslationWeights`
  (`rationalTranslationWeights`, Lemma II.1.2), and `G(F) × G(F)` acts on `L(ω, P)` by the
  representation of `productInducedCoefficientObject`.
- **`rationalInducedCoefficientMap_rationalInducedFourierTransform f g`** (Lemma VII.1.1 (iii)):
  `(E_P^G f̂(ω, P))(g) = d(ω) θ_π(λ(g) f̌)`, with `E_P^G = rationalInducedCoefficientMap` (Unit 19),
  `d(ω) = representationFormalDegree` and `θ_π = schwartzCharacter` for `π = I_P^G A`.
- **`integral_conj_rationalInducedCoefficientMap_mul_eq_inner ψ f`** (Lemma VII.1.1 (ii)), for an
  inverse-invariant `mu`: `∫ conj((E_P^G ψ)(g)) f(g) d(mu) = (ψ, f̂(ω, P))`. Here `( , )` is the
  product of V.2 on `L(ω, P)` (`CompactInduction.formalDegreeProductForm`).
- **`rationalInducedFourierTransform_eq_of_forall_integral f φ hφ`**: if
  `(E_P^G ψ, f)_G = (ψ, φ)` for every `ψ ∈ L(ω, P)`, then `φ = f̂(ω, P)`.

## Proofs

- Cofinality: `K.comap M_I(F).subtype` is an open subgroup of `M_I(F)` with compact carrier, so
  `CompactOpenSubgroup 𝐌` is nonempty and `CompactOpenSubgroup.cofinal (G := 𝐌)` applies.
- (i) and (iii) apply `inducedFourierTransform_translate` and
  `coefficientMap_inducedFourierTransform` with the same actual data as the definition. The
  definitions are unfolded (`rationalInducedFourierTransform`, and `rationalInducedCoefficientMap`
  for (iii)), and the final step is `with_reducible_and_instances exact`, as in Units 19–21.
- (ii) applies `integral_conj_coefficientMap_mul_eq_inner` in the same way.
- Uniqueness repeats, on actual points, the Library's proof of
  `inducedFourierTransform_eq_of_forall_integral`. By (ii) and `hφ`, the positive definite
  product satisfies `(ψ, f̂(ω, P)) = (ψ, φ)` for all `ψ`. Then `(f̂ − φ, f̂ − φ) = 0`, and
  definiteness gives `f̂(ω, P) = φ`.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered; Waldspurger allows semi-standard `P`.
- The conclusion of Lemma II.1.5 (`hsw`) and the temperedness of `ω` (`hTA`) are hypotheses. The
  first is the published, unproved `RationalXiSquareIntegrableStatement`. For square-integrable
  `ω` the second follows from the published, unproved
  `RationalSquareIntegrableRapidDecayStatement` (Corollary III.1.2); this deduction is not
  formalized here.
- `K`, `hPK`, `hM`, `ρ`, `hρ`, `hKρ` are data (ledger rows S3, S4, S5).
- Lemma VII.1.2 and Proposition VII.1.3 (`ψ_f[O, P] ∈ C^∞(O, P)`) are not treated on actual
  points here.
