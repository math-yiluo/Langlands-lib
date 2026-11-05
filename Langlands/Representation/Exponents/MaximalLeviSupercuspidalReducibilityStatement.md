# Reducibility of representations induced from supercuspidals of maximal Levis

Author: Worker 6. Module `Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `MaximalLeviSupercuspidalReducibilityStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.1.3, printed pp.224–226 / PDF pp.230–232. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The setting: `M` is a maximal standard Levi subgroup, i.e. a Levi factor of a maximal proper parabolic. Then `W(M, *) = {g ∈ G | g M g⁻¹ is a standard Levi subgroup} / M` has two elements `{1, w}`, and `M' = w·M`. The theorem says: let `P = MN` be as above and `(ρ, W)` an irreducible supercuspidal representation of `M`. Put `ρ' = ρ^w`. Suppose that `i_P^G(ρ, W)` is reducible. Then `M = M'`, and `ρ' = ρψ` for some unramified character `ψ` of `M` with values in `ℝ_{>0}`.

This is a **derived** formulation: the parabolic is an arbitrary actual maximal rational parabolic, and the conclusion "`M = M'` and `ρ^w = ρψ`" is stated through an element of `G(F)` that normalizes the Levi and lies outside it. See "Faithfulness notes".

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`.

It then quantifies over every actual rational parabolic `p : P ⟶ G` (`hp : IsParabolicSubgroup p`), rational Levi `l : M ⟶ P` (`hl`) and matching geometric unipotent radical `r : U ⟶ P` (`hr`, `hmul : IsIso (subgroupMultiplication l r)`), subject to:

- **properness:** `¬ IsIso p`;
- **maximality:** for every group scheme `Q`, every `q : Q ⟶ G` with `IsParabolicSubgroup q` and every `j : P ⟶ Q` with `j ≫ q = p`, either `IsIso j` or `IsIso q`. So no parabolic lies strictly between `P` and `G`.

On `rationalPoints M` it installs the canonical topology `leviPointTopology l hl` and the derived instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl` from the published `ArbitraryParabolicLeviPoints`. For every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` it assumes:

- `ρ.IsIrreducible`;
- **supercuspidality:** for every actual rational parabolic `p' : P' ⟶ M` of `M` with rational Levi `l'`, matching radical `r'` and `hmul'`, if `¬ IsIso p'` then the carrier of the published normalized Jacquet module `(jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ` is a subsingleton, i.e. zero;
- **reducibility:** `¬ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).IsIrreducible`.

It concludes that there are `g : rationalPoints G` and an automorphism `φ : M ≅ M` of group schemes with

- `φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom` and `g ∉ pointImage (l ≫ p)`;
- an element `ψ` of the published `Plancherel.unramifiedCharacters (fun χ => (Plancherel.rationalNormCharacters M χ).toMul)` such that every value `ψ m` is a positive real number;
- a linear equivalence `T : ρ ≃ₗ[ℂ] ρ` with `T (ρ m x) = ψ(φ(m)) • ρ(φ(m)) (T x)` for all `m : rationalPoints M` and `x : ρ`, where `φ(m)` abbreviates `rationalPoints.map φ.hom m`.

## The objects

- `G.innerIso g` acts on points as `x ↦ g x g⁻¹` (published `rationalPoints_map_innerIso`). The first condition says that conjugation by `g` preserves the image of `M` and induces `φ` on it, so `g` normalizes the Levi. With `g ∉ pointImage (l ≫ p)`, its class in `N_G(M)(F)/M(F)` is nontrivial.
- `Plancherel.unramifiedCharacters ν` is the published group of continuous characters `M(F) →ₜ* ℂˣ` trivial on the common kernel of the normalized absolute values `|χ|_F` of all rational characters `χ` of `M`. This is Renard's group of unramified characters, trivial on `⁰M`.
- The condition on `T` says `ρ^g ≃ ρψ`. Here `ρ^g(m') = ρ(g⁻¹ m' g) = ρ(φ⁻¹(m'))`. An intertwiner `T` from `ρ^g` to `ρψ` satisfies `T ρ^g(m') = ψ(m') ρ(m') T`, and putting `m' = φ(m)` gives the displayed identity.
- `jacquetFunctor` for the parabolic `p'` of `M` is the published normalized Jacquet functor, with `M` as the ambient group. Its normalization does not affect vanishing.

## Faithfulness notes

- **Maximal parabolics.** The source fixes a maximal *standard* Levi. The statement allows every actual maximal proper parabolic with any rational Levi. This is equivalent by `G(F)`-conjugation, which preserves supercuspidality, irreducibility of the induced representation and the conclusion.
- **The conclusion.** `N_G(M)(F)/M(F)` embeds in `W(M, *)`, and `W(M, *) = {1, w}` (V.4.4, V.4.8). So some `g ∉ M(F)` normalizes `M` if and only if `w` normalizes `M`, that is `M = M'`, and then `g` represents `w` and `ρ^g ≃ ρ^w`. The statement's conclusion is therefore equivalent to the source's "`M = M'` and `ρ' = ρψ`". The source writes `ρ' = ρψ` for an isomorphism of representations. The statement asserts an isomorphism `T`, not an equality of actions.
- **Supercuspidality.** Renard's definition (VI.2.1, printed p.137 / PDF p.143) is the vanishing of `r_P V` for every proper parabolic of the group. The statement uses the normalized Jacquet module for every actual proper parabolic of `M` with a rational Levi and matching radical. Twisting by the modulus does not change vanishing, and by Remark 1 of VI.2.1 standard parabolics would suffice.
- **Unramified positive characters.** "À valeurs dans `ℝ*₊`" is the condition that each value is a positive real number.
- **No other hypotheses.** No unitarity of the central character is assumed. The source proof reduces to that case by an unramified twist of `G`.

## Remaining obligations

The proof is a separate obligation. The source route uses the reduction to a unitary central character by a twist (VI.8.5, III.2.11); the geometric lemma and the Jacquet modules of `i_P^G ρ` (VI.5.3); the length bound (VI.5.4); Frobenius reciprocity; faithfulness of the functor `R` of VI.7.2; unitarity of unitary supercuspidals; Casselman's criterion (published statement `ArbitraryParabolicCasselmanCriterionStatement`) applied to a constituent; the duality (VI.9.6.2) of Jacquet modules; and the decomposition `ρ = ψ ρ₀` with `ρ₀` unitary supercuspidal and `ψ` real (VI.8.5). It also needs the structural facts about `W(M, *)` and `N_G(M)` for actual reductive groups. The Corollary of VII.1.3 (equivalence of Bernstein blocks for `w·D ≠ D`) is not part of this statement.

## Provenance

This is a derived statement of the Theorem of VII.1.3 for the represented-parabolic interface. Induction is the published `leviInductionFunctor`, Jacquet modules of `M` are the published `jacquetFunctor`, and unramified characters are the published `Plancherel.unramifiedCharacters` for the rational norm characters of `M`. Allowing arbitrary maximal parabolics and expressing `M = M'` through a normalizing element outside `M(F)` are formalization choices explained above.
