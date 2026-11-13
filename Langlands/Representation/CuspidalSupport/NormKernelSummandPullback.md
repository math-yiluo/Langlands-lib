# Pulling back the compact induction of a norm-kernel summand along an automorphism

Author: Worker 5226. This is an internal construction with supporting results. It was derived for the planned proof of the free-module conjunct of the Lemma of Renard VI.10.4 (printed pp.209–212 / PDF pp.215–218). Reference: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Relation to Renard

In the proof of the Lemma (printed p.210 / PDF p.216), Renard filters `r_D i_P^G(Π_D)` with successive quotients `w·Π_D` for `w ∈ W(D)`, and then writes "Or, si `w ∈ W(D)`, `w·Π_D ≃ Π_D`" without further proof. Here `Π_D = ind_{⁰M}^M(ρ₀)` with `ρ₀` an irreducible summand of the restriction of an irreducible supercuspidal `π` to `⁰M`.

- `nonempty_pullback_rationalNormKernelSummandInduction_iso` proves that assertion for an actual automorphism `e` of the rational points that preserves `⁰M`. The proof is the author's; it uses Renard VI.3.2.
- `exists_pullback_iso_twist_of_hom_ne_zero` is not in Renard. Renard removes the pieces with `w ∉ W(D)` by the block projection `r_D` (with (V.4.3.3) and VI.5.3(iii)). The author's planned proof works with all pieces of the geometric-lemma filtration instead. It needs to know that a piece `w·Π_D` with `w ∉ W(D)` has no nonzero map to `Π_D`, and this theorem gives the contrapositive.

The other declarations are general facts about compact induction from an open normal subgroup. Renard does not state them.

## Setting of the general part

- `G` is a topological group and `H` an open normal subgroup (`IsOpen (H : Set G)` is assumed only where needed).
- `e : G ≃ₜ* G` is a topological group automorphism with `he : ∀ x, e x ∈ H ↔ x ∈ H`.
- `SmoothRep.pullback e A` is `A` with the action `g ↦ A(e g)` on the same carrier.
- `Induction.compactInductionFunctor H` is compact induction `c-ind_H^G` from smooth representations of `H`.
- `Induction.automorphismInducing H e he σ` is `σ ∘ e|_H` (from `Induction/CompactAutomorphism.lean`).
- `SmoothRep.normalSubgroupInverseConjugation H g` is the automorphism `h ↦ g⁻¹ h g` of `H`.

## Declarations

### Algebra (`section Algebra`)

For a field `k`, a monoid `Γ` and representations `σ`, `τ`, `υ` of `Γ` over `k`:

- `intertwiningRangeEquiv J hJ`: an injective intertwiner `J : σ → τ` gives an equivalence from `σ` to its range, viewed as a subrepresentation of `τ`. It is `LinearEquiv.ofInjective`. `intertwiningRangeEquiv_apply` (by `rfl`) says the image of `v` is `J v`.
- `isIrreducible_of_representationEquiv E hσ`: an equivalence `E : σ ≃ τ` carries irreducibility of `σ` to `τ`. The proof uses `Representation.irreducible_iff_isSimpleModule_asModule` and `LinearMap.isSimpleModule_iff_of_bijective`.
- `exists_intertwining_ne_zero_of_semisimple hτ J hJ T hT`: let `τ` be semisimple, `J : σ → τ` injective and `T : σ → υ` nonzero. Then some intertwiner `τ → υ` is nonzero. The proof takes a complement `S'` of the range of `J` (`exists_isCompl`), projects `τ` onto the range along `S'` (`Langlands.subrepresentationProjection`), and composes with the inverse of `intertwiningRangeEquiv J hJ` and then with `T`. On `J v` the composite is `T v`, so it is nonzero.

### Compact induction and automorphisms (`section General`)

- `inverseConjugation g : G ≃ₜ* G` is `x ↦ g⁻¹ x g`; `inverseConjugation_apply` unfolds it. `inverseConjugation_mem_iff` shows that it preserves the normal subgroup `H`.
- `pullbackInverseConjugationIso g A : SmoothRep.pullback (inverseConjugation g) A ≅ A`, for `A : SmoothRep.{0, uG, uV} ℂ G`. Its underlying linear map is `A(g)`, with inverse `A(g⁻¹)`. It intertwines because `A(g) A(g⁻¹ h g) = A(h) A(g)`.
- `compactInductionPullbackIso H e he σ : pullback e (c-ind_H^G σ) ≅ c-ind_H^G (σ ∘ e|_H)`, for `σ : Rep ℂ H`. It is `SmoothRep.mkIso` applied to `Induction.precomposeCompactInducedEquiv H e he σ.ρ`, the equivalence `f ↦ f ∘ e` of `Induction/CompactAutomorphism.lean`.
- `compactInductionInverseConjugateIso H g σ : c-ind_H^G (σ ∘ conj_g) ≅ c-ind_H^G σ`, where `conj_g = normalSubgroupInverseConjugation H g`. It is the composite of
  - the identity iso identifying `σ ∘ conj_g` with `σ ∘ (inverseConjugation g)|_H` (the two actions agree by `rfl`),
  - the inverse of `compactInductionPullbackIso` for `inverseConjugation g`,
  - `pullbackInverseConjugationIso g`.
- `compactInductionPullbackIsoOfEquiv H e he σ g E : pullback e (c-ind_H^G σ) ≅ c-ind_H^G σ`, given an equivalence `E : σ ∘ e|_H ≃ σ ∘ conj_g`. This is the main definition of the file. It is `compactInductionPullbackIso`, then `c-ind_H^G` applied to `Rep.mkIso E`, then `compactInductionInverseConjugateIso H g σ`.
- `compactInducedEvaluationMap H σ π j x`, for `j : σ → π|_H` and `x : G`, is the `H`-intertwiner `F ↦ π(x⁻¹) j(F(x))` from `(c-ind_H^G σ)|_H` to `π|_H`. It intertwines because `F(x h) = σ(x h x⁻¹) F(x)` for `h ∈ H` (`x h x⁻¹ ∈ H` by normality) and `π(x⁻¹) π(x h x⁻¹) = π(h) π(x⁻¹)`. `compactInducedEvaluationMap_apply` (by `rfl`) unfolds it.
- `exists_intertwining_ne_zero_of_pullback_hom hH e he ρ π j hj f hf`: let `H` be open, `ρ` a smooth representation of `H`, `π` a smooth representation of `G` (both with carriers in universe `uV`), and `j : ρ ⟶ π|_H` injective. A nonzero `f : pullback e (c-ind_H^G ρ) ⟶ c-ind_H^G ρ` gives a nonzero `H`-intertwiner `T : ρ ∘ e|_H → π|_H`. The proof:
  - Let `Ψ` be the equivalence `pullback e (c-ind ρ) ≃ c-ind(ρ ∘ e|_H)`. Then `f' = f ∘ Ψ⁻¹` is a `G`-map `c-ind(ρ ∘ e|_H) → c-ind ρ`.
  - Its Frobenius partner is `φ = f'|_H ∘ unit : ρ ∘ e|_H → (c-ind ρ)|_H`. It is nonzero: by `Induction.cosetSum_resIntertwining_comp` and `Induction.cosetSum_unitMap`, `cosetSum φ = f'`, so `φ = 0` would force `f = 0`.
  - Pick `v` with `φ v ≠ 0` and `x` with `(φ v)(x) ≠ 0`. Then `T = compactInducedEvaluationMap H ρ π j x ∘ φ` sends `v` to `π(x⁻¹) j((φ v)(x))`, which is nonzero because `j` is injective and `π(x⁻¹)` is invertible.
- `exists_restriction_intertwining_ne_zero e he ρ π j hj hss T hT`: if `(π ∘ e)|_H` is semisimple and `T : ρ ∘ e|_H → π|_H` is nonzero, some intertwiner `(π ∘ e)|_H → π|_H` is nonzero. The map `j` is also an injective intertwiner `ρ ∘ e|_H → (π ∘ e)|_H` (same linear map), and `exists_intertwining_ne_zero_of_semisimple` applies.

### Rational points (`section Rational`)

Fix a nonarchimedean local field `F`, a connected reductive group scheme `G` over `F` (`hG`), and give the rational points `G(F)` the topology `rationalPointTopology F G.X`, the one used by `rationalNormKernelSummandInduction`. Let `⁰G = rationalCommonNormKernel G` and `Π = rationalNormKernelSummandInduction G ρ = c-ind_{⁰G}^{G(F)} ρ`. Let `π : SmoothRep.{0, uF, uV} ℂ G(F)` be irreducible, `ρ : SmoothRep.{0, uF, uV} ℂ ⁰G`, and `j : ρ ⟶ π|_{⁰G}` injective. Let `e : G(F) ≃ₜ* G(F)` preserve `⁰G` (`he`). The unramified characters are `unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)`, Renard's `X(G)`; the twist `π.twist χ hχ` acts by `g ↦ χ(g) π(g)`.

- `nonempty_pullback_rationalNormKernelSummandInduction_iso … hρ … χ hχ ψ`: assume `ρ` irreducible and an iso `ψ : pullback e π ≅ π.twist χ hχ`. Then `Nonempty (pullback e Π ≅ Π)`. The proof:
  - `J₁ = j : ρ → π|_{⁰G}` and `J₂ = ψ ∘ j : ρ ∘ e|_{⁰G} → π|_{⁰G}` are injective `⁰G`-intertwiners. For `J₂`, the twist is invisible on `⁰G`, because every unramified character is trivial on `⁰G` (`χ.property`).
  - `ρ ∘ e|_{⁰G}` is irreducible (`isIrreducible_comp_continuousMulEquiv_iff`), so the ranges of `J₁` and `J₂` are irreducible subrepresentations of `π|_{⁰G}`.
  - The third clause of `rationalNormKernelOrbit` (Renard VI.3.2(i)) gives `g` with the range of `J₁`, composed with `conj_g`, equivalent to the range of `J₂`.
  - Composing these equivalences (with `equivComp` to compose with `conj_g`) gives `E : ρ ∘ e|_{⁰G} ≃ ρ ∘ conj_g`, and `compactInductionPullbackIsoOfEquiv` gives the iso.
- `exists_pullback_iso_twist_of_hom_ne_zero … f hf`: a nonzero `f : pullback e Π ⟶ Π` gives some `χ : X(G)` with `Nonempty (pullback e π ≅ π.twist χ hχ)` for every proof `hχ` that `ker χ` is open. Irreducibility of `ρ` is not needed. The proof:
  - `exists_intertwining_ne_zero_of_pullback_hom` (with `⁰G` open, `isOpen_rationalCommonNormKernel`) gives a nonzero `ρ ∘ e|_{⁰G} → π|_{⁰G}`.
  - `pullback e π` is irreducible, so its restriction to `⁰G` is semisimple by the first clause of `rationalNormKernelFiniteRestriction` (Renard VI.3.2(ii)). `exists_restriction_intertwining_ne_zero` gives a nonzero `(π ∘ e)|_{⁰G} → π|_{⁰G}`.
  - `rationalNormKernelTwistEquivalence` (Renard VI.3.2(iii)) is applied twice. Its `C ⇒ A` direction for the pair (`pullback e π`, `π`) makes the two restrictions equivalent. Its `A ⇒ B` direction for (`π`, `pullback e π`), applied to the inverse equivalence, gives `χ` with `π ⊗ χ ≃ pullback e π`. `SmoothRep.mkIso` and `Iso.symm` turn this into the stated iso.

## Hypotheses and use

The automorphism condition `he` is assumed. In the planned application `e` is the map on rational points of an automorphism `φ : M ≅ M` of a Levi subgroup, and `he` comes from `mem_rationalCommonNormKernel_mapIso_iff` (`Geometry/Building/ValuationBuildingIsoTransport.lean`). That application is not part of this file.
