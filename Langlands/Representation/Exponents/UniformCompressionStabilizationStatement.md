# Renard VI.9.1: uniform stabilization and the generalized Jacquet lemma

Authors: Worker 937 and Worker 1587. Worker 937 supplied the original shared draft; Worker 1587 checked the current source correspondence and refined the scope explanation. Module `Langlands.Representation.Exponents.UniformCompressionStabilizationStatement`, namespace `Langlands.Aubert.General.RationalPointFamily`. Two statements, `UniformCompressionStabilizationStatement : Prop` and `GeneralizedJacquetLemmaStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.9.1, printed pp.195–197 / PDF pp.201–203. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The notion of a stable endomorphism is from Appendix C.II, printed pp.276–277 / PDF pp.282–283.

In translation, the source says:

- **Theorem of VI.9.1 (generalized Jacquet lemma).** Let `P = MN` be a parabolic subgroup of `G`, `(π, V)` a smooth representation of `G`, and `K` a compact open subgroup of `G` with an Iwahori decomposition relative to `P`. Then the projection `j : V → V_N` maps `V^K` onto `(V_N)^{K_M}`.
- **Proposition of VI.9.1.** Fix `t ∈ C_A^{++}` and let `A` be the endomorphism of `V^K` given by `a_{t,K} = e_K ∗ δ_t ∗ e_K`. Then `A` is eventually stable. More precisely, there is a constant `b = b(G, K)`, depending only on `G` and `K`, such that for every smooth representation `(π, V)` the endomorphism `A^b` of `V^K` is stable. With `V^K_0 = ker A^b` and `V^K_* = Im A^b`, one has `V^K = V^K_0 ⊕ V^K_*`.

The source deduces the Theorem from the Proposition and two lemmas on PDF p.203. The Proposition's proof occupies VI.9.2–VI.9.3, printed pp.198–200 / PDF pp.204–206, and uses the Bernstein decomposition (VI.7), the families of VI.8 and the uniform admissibility theorem VI.2.3.

## Setting

Both statements quantify over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. They install `hG.isAffineHom` and the canonical topology `pointTopology` on `rationalPoints G`, and assume `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`. This is the setting of the published `RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis` and of `LeviSecondAdjointnessStatement`.

The parabolic is the dynamic parabolic of a cocharacter `χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G`. On rational points:

- `N = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))`, the dynamic unipotent radical;
- `M = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))`, the centralizer of `χ`;
- `N̄ = (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))`, the opposite radical.

The statements then take a compact open subgroup `K` (an `OpenSubgroup` with `IsCompact`), and an element `g` of `G(k)` with two hypotheses:

- `g` commutes with every element of `M`;
- `Jacquet.IsIwahoriContraction K N M N̄ g`. Its fields say that `g ∈ M`, that `K = (K ∩ N̄)(K ∩ M)(K ∩ N)`, that conjugation by `g` maps `K ∩ N` into itself, that conjugation by `g⁻¹` maps `K ∩ M` and `K ∩ N̄` into themselves, that every element of `N` is conjugated into `K` by some power `g^r`, and that powers of `g⁻¹` contract `K ∩ N̄` into every open subgroup.

The element `g` plays the role of Renard's `t`. The orientation matches: Renard's proof uses that `N_i = t^{-i} K_N t^i` increase and exhaust `N` (PDF p.202), and the fields `upper` and `exhaust` say exactly this with `t = g`.

## The compressed action

For a smooth representation `ρ : Representation ℂ (rationalPoints G) V` with `hρ : IsSmooth ρ`, write `C = Jacquet.compressedAction ρ hρ K hK g`. It is the endomorphism `v ↦ e_K(ρ(g) v)` of `V^K = fixedVectors ρ K.toSubgroup`, where `e_K` is the normalized average over `K`. This is the action of `a_{g,K} = e_K ∗ δ_g ∗ e_K` on `V^K`, the source's `A`. The published submodules of `V^K` are

- `Jacquet.stableImage ρ hρ K hK g = ⨅ r : ℕ, range (C ^ r)`;
- `Jacquet.powerKernelSup ρ hρ K hK g = ⨆ r : ℕ, ker (C ^ r)`;

and `Jacquet.CompactCompressionSplits ρ hρ K hK g` is `IsCompl (powerKernelSup …) (stableImage …)`.

## `UniformCompressionStabilizationStatement`

After the setting, `K`, `hK`, `g` and the two hypotheses on `g`, the statement asserts that there is `b : ℕ` such that for every `V : Type v` with `[AddCommGroup V] [Module ℂ V]`, every `ρ` and every `hρ : IsSmooth ρ`:

1. for every `s : ℕ` with `b ≤ s`, `stableImage ρ hρ K hK g = range (C ^ s)` and `powerKernelSup ρ hρ K hK g = ker (C ^ s)`;
2. `CompactCompressionSplits ρ hρ K hK g`.

The exponent `b` is chosen after `k`, `G`, the instances, `χ`, `K`, `g` and the hypotheses, and before the universe-`v` carrier and the representation. This retains the source's independence from `(π, V)`. Renard states the stronger dependence `b = b(G, K)`. The Lean quantifier order permits `b` to depend on the already fixed field, group, cocharacter, compact subgroup, contracting element, and universe parameters; it does not assert one exponent simultaneously for varying `χ` or `g`.

**Why these are the stability and direct-sum conclusions.** By C.II, an endomorphism `T` is stable when `ker T = ker T²` and `Im T = Im T²`. For a positive exponent `b`, stability of `A^b` gives `V^K = ker A^b ⊕ Im A^b` by C.II Lemma (i). On these summands `A` is respectively nilpotent (annihilated by `A^b`) and bijective, so the power kernels and ranges are constant for every `s ≥ b`. Monotonicity then identifies their constant values with the supremum of all power kernels and the intersection of all power ranges. Conversely, constancy from a positive `b` gives the two stability equalities by comparing `b` with `2b`, and C.II gives the direct sum. Thus the existential conclusion is equivalent to the source's positive stable-power and direct-sum formulation for each fixed set of parameters, with the uniformity just described.

Lean allows `b = 0`. This introduces no extra existential conclusion: a witness can always be increased to `max b 1`, retaining its uniformity and all the stated equalities. A zero witness itself forces all kernels to be zero and all ranges to be the whole fixed-vector space. The positive-exponent qualification is necessary when inferring stabilization from stability of `A^b`, since `A^0` is always the identity.

Item 2 is exactly `V^K = powerKernelSup ⊕ stableImage`; it follows from item 1 by C.II and is retained explicitly for downstream users. These comparisons are mathematical explanations, not proofs supplied by this statement module.

## `GeneralizedJacquetLemmaStatement`

After the setting, `K`, `IsCompact K`, `g` and the two hypotheses on `g`, it asserts for every `V : Type v` with `[AddCommGroup V] [Module ℂ V]`, every `ρ` and every proof of `IsSmooth ρ` that

`Function.Surjective (Jacquet.fixedJacquetMap ρ N M (Dynamic.centralizer_le_normalizer_unipotent χ (Over.mk (𝟙 _))) K.toSubgroup)`.

The published `fixedJacquetMap ρ N M hMN K` maps `V^K` to the vectors of the Jacquet module `V_N` fixed by `K ∩ M` (the preimage `K.comap M.subtype`), by the coinvariant quotient map. The action on `V_N` is unnormalized. Normalization would not change the fixed vectors, since the modulus character is trivial on the compact group `K ∩ M`. The normalizing proof `Dynamic.centralizer_le_normalizer_unipotent χ (Over.mk (𝟙 _))` is the published proof that `M` normalizes `N`.

## Faithfulness and scope

- **Parabolics.** The statements use dynamic parabolics `P_G(χ)` with their centralizer Levi and opposite radical. The comparison with arbitrary represented parabolics is the separate Library target `Langlands.GroupScheme.ParabolicDynamicStatement` and is not assumed by these statements. Transport to represented parabolics is not part of these statements.
- **The contracting element.** The source fixes `t ∈ C_A^{++}`, a strictly dominant element of the split component `A` of `M`, and assumes an Iwahori decomposition of `K`. The Lean statements instead accept any `g` that is central in `M(k)` and satisfies `IsIwahoriContraction K N M N̄ g`. This is a **derived** generalization: the source's argument uses about `t` only the Iwahori factorization, the contraction properties above and centrality in `M`. Centrality makes `π_N(g)` an invertible `M`-endomorphism of `V_N`, preserving its `K ∩ M`-fixed vectors; the factorization, exhaustion and contraction hypotheses give the same intertwining, kernel and localization arguments of PDF pp.202–203. In VI.9.2–VI.9.3 the compressed action is linear over the coefficient algebra of each induced family, and its localized action is this invertible Jacquet action. The finite-module, specialization and exact-sequence arguments use these properties, while the uniform-admissibility bound is independent of the chosen operator. These are the reasons for accepting any such `g` as a derived target; the adaptation remains a separate proof obligation. The published `BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint` and `dynamic_hasOppositeIwahoriContractionBasis` supply such `g` with arbitrarily small `K`.
- **The Theorem's hypothesis on `K`.** The source assumes only an Iwahori decomposition of `K`. The Lean statement assumes the stronger existence of a contracting `g` for `K` as above. So `GeneralizedJacquetLemmaStatement` covers fewer subgroups `K` than the source's Theorem; it covers all `K` used by the second adjointness argument, which works with a basis of such subgroups.
- **No finiteness.** No admissibility, finite length or finite generation is assumed. This is the point of VI.9.1 compared with VI.6.1.
- **Universes.** The source does not consider universes. Each statement fixes a carrier universe `v`, independent of the universe `u` of `k`. In `UniformCompressionStabilizationStatement` the exponent `b` is chosen before the carrier, so it is uniform over all carriers in `Type v`.
- **Omitted parts.** The source's further claims are not stated: the identification of the localization of `V^K` at `A` with `(V^K_*, A|V^K_*)`, the bound `b ≤ c(G, K)` by the constant of the uniform admissibility theorem VI.2.3, and Remarks 1–3 of PDF pp.203–204 (independence of `t`, description by compact subgroups `C`, `C̄`, and the range `A^+(ε)`).

## Remaining obligations

Both proofs are separate obligations. The source proves the Theorem from the Proposition, the lemma `V(N) ∩ V^K = ⋃ ker A^i` and the localization lemma (PDF pp.202–203). The Proposition needs the Bernstein decomposition, the families of VI.8 and uniform admissibility VI.2.3.

## Provenance

This is a derived formulation of the Theorem and the Proposition of Renard VI.9.1. It uses the published compressed action, stable image, kernel supremum, splitting predicate and fixed-vector Jacquet map of namespace `Langlands.Jacquet`, and the published dynamic parabolic subgroups. The Lean file introduces exactly these two Prop-valued definitions, with universe parameters `u` and `v`; it supplies no proof of either definition. The draft was shared by Worker 937 in revision 1 of this task and is reused with attribution.
