# Second adjointness and completion

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviCompletionOppositeJacquetStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviCompletionOppositeJacquetStatement : Prop`; nothing is proved here. The completions are the definitions of `Langlands.Representation.Smooth.CompactCompletion`, submitted with this statement.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.9.7, Theorem, printed p.205 / PDF p.211, with its proof on printed pp.205–206 / PDF pp.211–212. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation:

> Let `P = MN` be a parabolic subgroup of `G` and let `P̄ = M N̄` be the opposite parabolic subgroup. Then for every representation `(π, V)` in `M(G)` there is a natural isomorphism
>
> `φ : V̄^N ≃ \overline{V_{N̄}}`.
>
> For every `v ∈ V̄^N`, `φ(v)` is characterized by the following property: for every compact open subgroup `K` of `G` admitting an Iwahori decomposition along `P`, `φ(e_K · v) = e_{K_M} · φ(v)`.

Here `V̄` is the completion of I.1.4 (printed p.9 / PDF p.15) and `\overline{V_{N̄}}` that of the Jacquet module `V_{N̄}` as a representation of `M`. The proof makes the characterization explicit. It writes `\overline{V_{N̄}} = lim_K V_{N̄}^{K_M}` and `V̄ = lim_K V^K`, and uses the subspace `V^K_*` of `V^K` on which the Jacquet map `j_{N̄}` is an isomorphism `V^K_* ≃ V_{N̄}^{K_M}` (VI.9.1 with the roles of `P` and `P̄` exchanged). So `e_{K_M}·φ(v)` is `j_{N̄}(e_K·v)`. The Iwahori decomposition is that of V.5.2 (printed p.123 / PDF p.129): `K = K_{N̄} K_M K_N` with `K_N = K ∩ N`, `K_M = K ∩ M`, `K_{N̄} = K ∩ N̄`, together with the contraction properties of `C_A^+` and `C_A^-` stated there.

This is a **derived** formulation (see "Provenance").

## Statement

The ambient data are those of the published `LeviSecondAdjointnessStatement` and `LeviJacquetContragredientStatement` (VI.9.6). The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`. It quantifies over two actual rational parabolic triples with the same Levi group scheme `M`:

- `P = MN`: `p : P ⟶ G`, `m : M ⟶ P`, `n : N ⟶ P` with `hp : IsParabolicSubgroup p`, `hm : IsRationalLeviSubgroup m`, and unnamed hypotheses `LeviSubgroup.IsGeometricUnipotentRadical n` and `IsIso (subgroupMultiplication m n)`;
- `P̄ = M N̄`: `pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar` with `hpbar`, `hmbar`, `hnbar`, `hmulbar`.

It assumes `mbar ≫ pbar = m ≫ p` and `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`. The Markdown of `LeviSecondAdjointnessStatement` explains why these hypotheses characterize the opposite parabolic. On `rationalPoints M` it installs `hm.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology m hm`, and the derived instances `leviPoints_locallyCompactSpace p m hp hm` and `leviPoints_nonarchimedeanGroup p m hp hm`.

Notation in the statement:

- `rPbar` is `leviJacquetFunctor pbar mbar nbar …`, Renard's normalized `r_{P̄}^G`. For a smooth `π` the space of `rPbar.obj π` is the space of `N̄(F)`-coinvariants `V_{N̄}`.
- `NG`, `NbarG` and `MG` are `pointImage (n ≫ p)`, `pointImage (nbar ≫ pbar)` and `pointImage (m ≫ p)`, the subgroups `N(F)`, `N̄(F)` and `M(F)` of `G(F)`.
- `incM y` is `leviPointsEquiv pbar mbar hpbar hmbar y`, viewed in `G(F)`. This is the point map of `mbar ≫ pbar = m ≫ p`, a topological-group isomorphism of `M(F)` onto `MG`.
- `x_K` denotes the `K`-component of a family `x`, for a compact open subgroup `K` (`Langlands.HarishChandraSchwartz.CompactOpenSubgroup`).

The statement asserts that there is a family of `ℂ`-linear isomorphisms, one for every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` with arbitrary carrier universe `v`,

`φ π : completionFixed π.representation π.isSmooth NG ≃ₗ[ℂ] completion (rPbar.obj π).representation (rPbar.obj π).isSmooth`,

that is `φ_π : V̄^N ≃ \overline{r_{P̄}^G(V)}`, with the following two properties.

- **Characterization.** For every `π`, every `x ∈ V̄^N`, every compact open subgroup `K` of `G(F)` and every `g ∈ G(F)` such that `g` commutes with every element of `MG` and `Jacquet.IsIwahoriContraction K.1 NbarG MG NG g` holds, and for every compact open subgroup `KM` of `M(F)` with `y ∈ KM ↔ incM y ∈ K` for all `y`:

  `(φ π x)_{KM} = Jacquet.Localization.mk π.representation NbarG 1 (x_K)`.

  The right side is the class of `x_K ∈ V^K` in the `N̄(F)`-coinvariants, that is `j_{N̄}(e_K·x)`. The left side is the `K_M`-component of `φ(x)`, that is `e_{K_M}·φ(x)`.
- **Naturality.** For every morphism `f : π ⟶ σ`, every `x ∈ V̄^N` and every `y ∈ W̄^N` (where `W` is the space of `σ`) such that `y_K = f(x_K)` for every compact open `K` of `G(F)`, and for every compact open `KM` of `M(F)`:

  `(φ σ y)_{KM} = r_{P̄}^G(f)((φ π x)_{KM})`,

  where `r_{P̄}^G(f)` is `SmoothRep.hom (rPbar.map f)`.

## The subgroups `K`

`Jacquet.IsIwahoriContraction K N' M' N̄' g` is the published structure used by `GeneralizedJacquetLemmaStatement`. Here it is applied with `N' = NbarG`, `M' = MG` and `N̄' = NG`, that is, with the roles of `P` and `P̄` exchanged, as the source prescribes in the proof ("il faut inverser les rôles de `P̄` et `P`"). Its fields say:

- `g ∈ M(F)`; with the commutation hypothesis, `g` is central in `M(F)`;
- every `k ∈ K` is `l m u` with `l ∈ K ∩ N(F)`, `m ∈ K ∩ M(F)`, `u ∈ K ∩ N̄(F)`. Since `K` is a group, taking inverses shows this is equivalent to the source's order `K = K_{N̄} K_M K_N`;
- conjugation by `g` maps `K ∩ N̄(F)` into itself, and conjugation by `g⁻¹` maps `K ∩ M(F)` and `K ∩ N(F)` into themselves;
- every element of `N̄(F)` is conjugated into `K` by some power `g^r`, and powers of `g⁻¹` contract `K ∩ N(F)` uniformly into every open subgroup.

For an element `t ∈ C_A^{++}` and a subgroup `K` as in V.5.2, the element `g = t⁻¹` has these properties by V.5.2 (ii)–(iv). So the characterization applies to the subgroups of V.5.2, which form a basis of neighbourhoods of the identity.

## Faithfulness notes

- **The class of `K`.** The source quantifies over all `K` admitting an Iwahori decomposition along `P`, a notion that in V.5.2 includes the contraction properties of `C_A^±`. The statement quantifies over the `K` for which some `g` central in `M(F)` satisfies `IsIwahoriContraction`. This is the convention of the published `GeneralizedJacquetLemmaStatement`, whose Markdown explains it: the source's argument uses about the contracting element only these properties. The element `g` only certifies that `K` belongs to the class; it does not occur in the conclusion.
- **`K_M`.** The source's `K_M = K ∩ M`. The statement quantifies over every compact open subgroup `KM` of `M(F)` whose image under `incM` is `K ∩ M(F)`. Such a `KM` is unique, and it exists because `incM` is a homeomorphism onto `MG`; the statement asserts neither fact.
- **"Characterized".** The statement asserts the characterizing property but not uniqueness. The property determines `φ(x)` once the subgroups `K ∩ M(F)` of the class are cofinal among the compact open subgroups of `M(F)`, which is how the source uses it ("les `e_{K_M}` forment un système filtrant d'idempotents"). This cofinality is not asserted.
- **Normalization.** The source writes `\overline{V_{N̄}}`, the completion of the unnormalized Jacquet module. The statement uses the completion of the normalized `r_{P̄}^G(V) = V_{N̄} ⊗ δ_{P̄}^{1/2}`. The two representations have the same space, and the modulus character is trivial on compact subgroups, so the averages `e_{K_M}` agree and the two completions are the same subspace of families. This comparison is not proved in Lean.
- **Naturality.** The source asserts that `φ` is natural. The completion of a morphism `f` is the componentwise map `f̄(m̄)(e) = f(m̄(e))` (I.1.5, printed p.10 / PDF p.16). The naturality clause says `φ_σ(f̄(x)) = \overline{r_{P̄}^G(f)}(φ_π(x))` without constructing `f̄`: it is stated for every `y` whose components are the images of those of `x`. The Lean development does not prove that the componentwise image of `x` lies in `W̄^N`.
- **Not asserted.** The statement does not assert that `φ` is `M(F)`-equivariant; the source's Theorem does not state this either. The consequences drawn after the proof, the isomorphism `r_{P̄}^G π̃ ≃ (r_P^G π)~` and a second derivation of second adjointness, are the published `LeviJacquetContragredientStatement` and `LeviSecondAdjointnessStatement`. No implication between these statements is asserted.
- **No admissibility.** As in the source, `π` is an arbitrary smooth representation.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `M(F)` are derived from them.

## Remaining obligations

The proof is a separate obligation. The source argues as follows. The `e_{K_M}` are cofinal, so `\overline{V_{N̄}} = lim_K V_{N̄}^{K_M}`. VI.9.1 (with `P` and `P̄` exchanged) gives `V^K_* ⊂ V^K` with `j_{N̄} : V^K_* ≃ V_{N̄}^{K_M}`, whence `\overline{V_{N̄}} ≃ lim_K V^K_* ⊂ V̄`. Using the second Remark of VI.9.1, `V^K_* = e_K e_C · V` for every sufficiently large compact open subgroup `C` of `N`, the image `V_*` is identified with the `v ∈ V̄` with `v ∈ e_C · V̄` for every compact open `C ⊂ N`, which is `V̄^N` because `N` is the union of its compact open subgroups. A Lean proof needs the generalized Jacquet lemma VI.9.1 and its Remarks for actual rational parabolics, cofinality of the subgroups `K` above, and the comparisons noted in "Faithfulness notes".

## Provenance

This is a derived statement of the Theorem of VI.9.7 for the represented-parabolic interface. The functor is the published normalized `leviJacquetFunctor`. The opposite parabolic is given, as in the published VI.9.6 statements, by an actual rational parabolic triple with the same Levi whose rational points meet those of `P` exactly in the Levi image. The completions are realized by the families of `CompactCompletion`, indexed by compact open subgroups as in the source proof. The class of subgroups `K` follows the published `GeneralizedJacquetLemmaStatement`. The characterization `φ(e_K·v) = e_{K_M}·φ(v)` is written componentwise as `φ(v)_{K_M} = j_{N̄}(v_K)`, the form the source proof makes explicit.
