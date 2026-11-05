# Uniform `Ξ`-bound for unramified twists (Waldspurger, Lemma VI.2.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientTwistXi`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `InducedCoefficientXi` (Worker 249): `inducedIntegrandKernel`, `inducedIntegrandKernel_mul`;
  through it `InducedCoefficientBound` (`compactIntegral`,
  `LeviData.norm_compactIntegral_le_xi`), `SphericalLevi`/`Spherical` (`xi`, `LeviData`,
  `IsIwasawaPair`, `iwasawaFactor`, `exists_iwasawaFactor`, `leviComponent`),
  `LeviWeightIntegrability` (`leviXiWeight`), and Worker 200's
  `CompactProductInducedCoefficients` (`CompactInduction.integrand`,
  `CompactInduction.coefficientMap`, `CompactInduction.coefficientMap_integral`),
  `CompactProductCoefficientBounds` (`CompactInduction.compactValue`,
  `CompactInduction.integrand_factorization`, `coefficientTensorMap_bound_finite`) and
  `CompactCoefficientHaarComparison` (`CompactInduction.measure_eq_normalizedHaar`);
- `Langlands.Representation.Plancherel.ProductCompactPicture` (Worker 200):
  `ProductInducedCompactPicture`, `productInducedCompactEquiv`, `productInducedCompactEquiv_eval`,
  `productCompactTwistTensorEquiv`, `productCompactTwistTensorEquiv_tmul`; through it
  `UnramifiedCharacters` (`unramifiedCharacters`, `unramifiedCharacter_isOpen_ker`) and
  `CoefficientTensors` (`coefficientTensorMap`, `coefficientTensorMap_tmul`);
- `Langlands.Representation.Category.Twist`: `SmoothRep.twist`,
  `SmoothRep.isAdmissible_twist_iff`;
- `Langlands.Representation.Plancherel.SmoothTensorFamilies` (Worker 200):
  `smoothFiniteTorusFunctions`, `finiteSmoothFamilies`, `mem_finiteSmoothFamilies_iff`; through it
  `IsSmoothFiniteTorusFunction.continuous`.

It also uses `closedHalfCharacter_eq_comp_projection` (module
`Langlands/Representation/Aubert/General/Parabolic`) and
`Induction.eval_isLocallyConstant`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus 234.

Lemma VI.2.2, printed p. 298 (PDF p. 64): "Soit `ψ ∈ C^∞(O, P)`. Il existe `C > 0` tel que pour
tout `ω ∈ O` et tout `g ∈ G`, on ait l'inégalité `|(E_P^G ψ_ω)(g)| ≤ C Ξ(g)`." Proof: "On se
ramène facilement à prouver l'assertion suivante: soient `(ω, E) ∈ O`, `v ∈ I_{K∩P}^K E`,
`v̌ ∈ I_{K∩P}^K Ě`; alors il existe `C > 0` tel que pour tous `χ ∈ Im X(M)` et tout `g ∈ G`, on ait
`|⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩| ≤ C Ξ(g)`. Notons `v_χ` l'élément de `I_P^G E_χ` dont la restriction à
`K` est `v`. Pour tout `g ∈ G`, on a `⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩ = ∫_K ⟨v_χ(kg), v̌(k)⟩ dk =
∫_K χ δ_P^{1/2}(m_P(kg)) ⟨ω(m_P(kg)) v(k_P(kg)), v̌(k)⟩ dk.`" Printed p. 299 (PDF p. 65): "Quand
`k` et `g` varient, les éléments `v(k_P(kg))` de `E`, resp. `v̌(k)` de `Ě`, restent dans des
sous-espaces de dimension finie. D'après le Corollaire III.1.2, il existe donc `C > 0` tel que
[...] `|⟨ω(m_P(kg)) v(k_P(kg)), v̌(k)⟩| ≤ C Ξ^M(m_P(kg))`. Alors [...] et il reste à appliquer le
Lemme II.1.6."

VI.1, printed p. 296 (PDF p. 62): `L_K(ω, P) = I_{K∩P, K∩P}^{K×K}(E ⊗ Ě)`, and "Pour tout
`χ ∈ Im X(M)`, `L(ω ⊗ χ, P)` s'identifie à `L_K(ω, P)` par restriction à `K`." Worker 200's
`ProductInducedCompactPicture h K A` is this compact space and `productInducedCompactEquiv` this
identification, for the product-induced coefficient space `L(ω ⊗ χ, P)` of the twist.

## What is proved, and the route

The module proves the reduced assertion of the proof, for a section `F₀` of the compact picture
(a sum of Waldspurger's `v ⊗ v̌`): one constant `C` bounds, for every unitary unramified `χ`, the
coefficient of `I_P^G(A ⊗ χ)` attached to the transport of `F₀` by `C Ξ(g)`. The route follows
Waldspurger's: the integrand of the coefficient at `k` is `δ_P^{1/2}(m_P(q)) χ(m_P(q))` times a
coefficient of `A` at `m_P(q)` of one of the finitely many values of `F₀` on `K × K`, where
`k g = q k₁`; `|χ| = 1`, the conclusion of Cor. III.1.2 for these finitely many values gives one
constant, and Lemma II.1.6 (through `LeviData.norm_compactIntegral_le_xi`) finishes.

It then proves the bound for the smooth families of VI.1 read in the compact picture: by
`mem_finiteSmoothFamilies_iff` (Worker 200's `SmoothTensorFamilies`), a family in
`finiteSmoothFamilies J (ProductInducedCompactPicture h K A)` is `z ↦ ∑ᵢ fᵢ(z) vᵢ` with finitely
many smooth `fᵢ` on the compact torus `(S¹)^J`, which are bounded; by linearity the coefficient of
the twisted section is `∑ᵢ fᵢ(e χ)` times coefficients of the fixed sections `vᵢ`, each bounded
by the first part. This is Waldspurger's "on se ramène facilement" for families given in this
form. The identification of a `ψ ∈ C^∞(O, P)` with such a family over every point of `O` (the
stabilizer invariance and the choice of representatives) is Worker 200's construction of VI.1
and is not repeated here.

## Scope and hypotheses

Characters: `ν : I → (M →* ℝ≥0ˣ)` is a family of positive characters of `M` (in the application
the norms of the rational characters, so that `unramifiedCharacters ν` is `X(M)`), and
`χ : unramifiedCharacters ν` is a continuous character `M → ℂˣ` trivial on their common kernel;
"unitary" is `∀ m, ‖(χ m : ℂ)‖ = 1` (Waldspurger's `χ ∈ Im X(M)`). `A ⊗ χ` is
`A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)`.

**Section `Tensor`.** `G` is a nonarchimedean topological group, `M` a subgroup, `ν` as above.

- `coefficientTensorMap_twist`: `χ`, a smooth complex representation `A` of `M`, a coefficient
  tensor `t` of `A ⊗ χ` and `m ∈ M`; no further hypotheses.

**Section `Compact`.** Moreover `G` is locally compact; `P, M, U` are subgroups with
`h : IsSemidirectDecomposition P M U`, `hU : IsClosed (U : Set G)`, `K` an open subgroup, and the
hypotheses of `productInducedCompactEquiv`: `hP : IsClosed (P : Set G)`,
`hK : IsCompact (K : Set G)`, `hν : ∀ i, Continuous (ν i)`, `hr : Continuous h.projection`,
`hPK : ∀ g, ∃ p : P, ∃ k : K, g = p k`.

- `twistedSection` (definition), `compactValue_twistedSection`: those hypotheses.
- `compactPicture_eval_range_finite`: only `hK` (and the group, `h`, `A`, `K`; local compactness
  is omitted).
- `integrand_twist_bound`: those hypotheses, `[SecondCountableTopology G]`,
  `hδ : IsUnimodularModulus U hU`, `ξ : M → ℝ` with `hξ : ∀ m, 0 ≤ ξ m`, the coefficient bound
  `hcoeff : ∀ v ℓ, ∃ C > 0, ∀ m, ‖ℓ(A(m) v)‖ ≤ C ξ(m)`, and `F₀`.

**`factorization_subtype`**: a group `G` with a topology, `P`, `K`, and
`hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q k`.

**Section `Xi`.** The data of `InducedCoefficientXi`: `G` locally compact, nonarchimedean,
second countable, Hausdorff, with its Borel structure; `h`, `hU`, `A`, `K`, `hK`; `ν`, `hν`;
`P₀`, `δ₀`, `δ₀^M`; `[CompactSpace K]`, `[CompactSpace (K ∩ M)]`.

- `norm_twist_coefficientMap_le_xi`: `[LocallyCompactSpace P]`, `hP`,
  `hm : Continuous h.projection`, `hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q k` (`G = P K`),
  `hG` (`G` unimodular), `hδP` (the modular character of `P` is the modulus of its action on
  `U`), `hA : A.IsAdmissible`, `hδ : IsUnimodularModulus U hU`, `hL : LeviData …`, `hP₀K`, `hMK`
  (the Iwasawa pairs `G = P₀ K`, `M = (P₀ ∩ M)(K ∩ M)`), `hδ₀`, `hcoeff` for `ξ = Ξ^M`
  (the conclusion of Cor. III.1.2 for `M`), and `F₀`. These are the hypotheses of
  `norm_coefficientMap_le_xi` (`InducedCoefficientXi`), with `ν`, `hν` added.
- `exists_norm_le_of_smoothFiniteTorusFunction`: a finite type `J` and a smooth function
  `f : smoothFiniteTorusFunctions J`; no further hypotheses.
- `norm_family_coefficientMap_le_xi`: the hypotheses of `norm_twist_coefficientMap_le_xi` except
  `F₀`, a finite type `J`, a family `Ψ : (J → Circle) → ProductInducedCompactPicture h K A` with
  `hΨ : Ψ ∈ finiteSmoothFamilies J _`, and any map `e : unramifiedCharacters ν → (J → Circle)`
  (in the application, torus coordinates of the unitary characters).

## Definitions

- `twistedSection h hU A K ν hP hK hν hr hPK χ F₀`: Waldspurger's `v_χ`, the element of the
  product-induced coefficient space of `A ⊗ χ` whose restriction to `K × K` is `F₀`
  (`(productInducedCompactEquiv … χ A).symm F₀`).

## Results

- `coefficientTensorMap_twist`: `ℓ((A ⊗ χ)(m) v) = χ(m) ℓ(A(m) v)` for coefficient tensors, with
  `ℓ` read as a functional of `A` by `productCompactTwistTensorEquiv`.
- `compactValue_twistedSection`: the values of `twistedSection … χ F₀` on `K × K` are the values
  of `F₀`, read through `(productCompactTwistTensorEquiv ν χ A).symm`.
- `compactPicture_eval_range_finite`: `F₀` takes finitely many values on `K × K`.
- `integrand_twist_bound` (**uniform integrand bound**): there is `C > 0` such that for every
  unitary `χ`, every `g`, `k`, `k₁ ∈ K` and `q ∈ P` with `k g = q k₁`, the integrand of the
  coefficient of `twistedSection … χ F₀` at `k` is at most `δ_P(m_P(q))^{1/2} C ξ(m_P(q))`.
- `factorization_subtype`: the two forms of `G = P K`.
- `norm_twist_coefficientMap_le_xi` (**Lemma VI.2.2, reduced form**): there is `C > 0` such that
  for every unitary unramified `χ` and every `g ∈ G`,
  `|coefficientMap(A ⊗ χ)(twistedSection … χ F₀)(g)| ≤ C Ξ(g)`.
- `exists_norm_le_of_smoothFiniteTorusFunction`: a smooth function on `(S¹)^J` is bounded.
- `norm_family_coefficientMap_le_xi` (**Lemma VI.2.2 for smooth families**): there is `C > 0`
  such that for every unitary unramified `χ` and every `g ∈ G`,
  `|coefficientMap(A ⊗ χ)(twistedSection … χ (Ψ (e χ)))(g)| ≤ C Ξ(g)`.

## Proof notes

1. `coefficientTensorMap_twist`: on `v ⊗ ℓ`, `(A ⊗ χ)(m) v = χ(m) A(m) v` and
   `productCompactTwistTensorEquiv` keeps `v` and the underlying functional of `ℓ`; induction on
   tensors (`TensorProduct.inductionOn`).
2. `compactValue_twistedSection`: `productInducedCompactEquiv_eval` applied to the inverse image
   of `F₀` and `apply_symm_apply`.
3. `compactPicture_eval_range_finite`: the evaluation of a smooth section is locally constant
   (`Induction.eval_isLocallyConstant`) on the compact group `K × K`.
4. `integrand_twist_bound`: `coefficientTensorMap_bound_finite` gives one `C` for the finitely
   many values of `F₀` (step 3). For each `χ`, `CompactInduction.integrand_factorization`
   writes the integrand as `δ_P^{1/2}(q)` times the coefficient of the compact value at
   `m_P(q)`; steps 2 and 1 replace that compact value by a value of `F₀` and a factor `χ(m_P(q))`
   of norm one; `closedHalfCharacter_eq_comp_projection` (unimodular `U`) gives
   `|δ_P^{1/2}(q)| = δ_P(m_P(q))^{1/2}`.
5. `norm_twist_coefficientMap_le_xi`: as in `norm_coefficientMap_le_xi`, the coefficient is
   `compactIntegral K (inducedIntegrandKernel …)` (`coefficientMap_integral`,
   `measure_eq_normalizedHaar`), the bound of step 4 with `ξ = Ξ^M`, read at the Iwasawa factor
   of `x` (`exists_iwasawaFactor`), bounds the kernel by `C leviXiWeight(x)`, and
   `LeviData.norm_compactIntegral_le_xi` (Lemma II.1.6) gives `C Ξ(g)`. The constant comes from
   step 4 and does not depend on `χ`.
6. `exists_norm_le_of_smoothFiniteTorusFunction`: `f` is continuous
   (`IsSmoothFiniteTorusFunction.continuous`) on the compact `(S¹)^J`, so its image is bounded.
7. `norm_family_coefficientMap_le_xi`: write `Ψ z = ∑ᵢ fᵢ(z) vᵢ` (`mem_finiteSmoothFamilies_iff`)
   and bound each `|fᵢ| ≤ Bᵢ` (step 6). The map `F₀ ↦ coefficientMap(…)(twistedSection … χ F₀)(g)`
   is linear (it is evaluation at `g` after `coefficientMap` after the inverse of
   `productInducedCompactEquiv`), so the coefficient is `∑ᵢ fᵢ(e χ)` times the coefficients of the
   `vᵢ`; step 5 for each `vᵢ` gives `Cᵢ`, and `C = 1 + ∑ᵢ Bᵢ Cᵢ`.

## Relation to the Library

- `norm_coefficientMap_le_xi` (`InducedCoefficientXi`) is the bound for one representation;
  this module makes the constant uniform over the unitary unramified twists, by reading all of
  them in Worker 200's fixed compact picture.
- `productInducedCompactEquiv` (`ProductCompactPicture`) is the identification of VI.1 by
  restriction to `K`; `finiteSmoothFamilies` and `mem_finiteSmoothFamilies_iff`
  (`SmoothTensorFamilies`) describe the smooth families in the compact picture, and
  `ProductInducedSmoothFamilies`, `ProductInducedOrbitSections` relate them to smooth sections
  over the orbit.

## Open obligations

Lemma VI.2.2 for `ψ ∈ C^∞(O, P)` as Waldspurger states it (the passage from such `ψ`, over
every point of `O`, to a smooth family in one compact picture), the conclusion of Corollary III.1.2 for `M` (the hypothesis `hcoeff`), the
specialization of `ν` to the rational-character norms of `M`, and the structural hypotheses
(`G = P K`, unimodularity, the Iwasawa pairs, `LeviData`) for Waldspurger's groups.
