# Well-definedness of the cuspidal support

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviCuspidalSupportAssociationStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviCuspidalSupportAssociationStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.7.1, Lemma, printed p.180 / PDF p.186, with its proof on the same page. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Lemma says: let `P_i = M_i N_i`, `i = 1, 2`, be parabolic subgroups of `G`, `(M_i, (ρ_i, W_i))` cuspidal data and `(π, V)` an irreducible smooth representation of `G` such that `(ρ_i, W_i)` is a composition factor of `r_{P_i}^G(π, V)`. Then the cuspidal data `(M_1, (ρ_1, W_1))` and `(M_2, (ρ_2, W_2))` are associated. The source uses the Lemma to define the cuspidal support map `Sc : Irr(G) → Ω(G)`.

Cuspidal data and association are defined in VI.5.2 (printed p.172 / PDF p.178): a cuspidal datum is a pair `(M, (ρ, W))` with `M` a Levi factor of a parabolic subgroup and `ρ` an irreducible supercuspidal representation of `M`; two data are associated if `g M_1 g⁻¹ = M_2` and `ρ_2 ≃ ρ_1^g` for some `g ∈ G`.

This is a **derived** formulation, because the functors are the published normalized functors of the represented-parabolic interface, supercuspidality is written out as the vanishing of normalized Jacquet modules, association is expressed through an isomorphism of group schemes, and a composition factor is read as an irreducible subquotient (see "Faithfulness notes").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over two actual rational parabolic triples `(p₁, l₁, r₁)` with Levi `M₁` and `(p₂, l₂, r₂)` with Levi `M₂`, each with its proofs `hpᵢ`, `hlᵢ`, `hrᵢ`, `hmulᵢ`, and installs on `rationalPoints Mᵢ` the affine instance, the canonical topology `leviPointTopology lᵢ hlᵢ` and the derived local-compactness and nonarchimedean-group instances.

For every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)`, `ρ₁ : SmoothRep.{0, u, v} ℂ (rationalPoints M₁)` and `ρ₂ : SmoothRep.{0, u, v} ℂ (rationalPoints M₂)` it assumes

- `π.IsIrreducible`;
- for each `i`: `ρᵢ.IsIrreducible`, `ρᵢ` is supercuspidal, and `SmoothRep.IsSubquotient ρᵢ ((leviJacquetFunctor pᵢ lᵢ rᵢ hpᵢ hrᵢ hlᵢ hmulᵢ).obj π)`;

and asserts that there are `g : rationalPoints G` and `φ : M₁ ≅ M₂` with

`φ.hom ≫ l₂ ≫ p₂ = l₁ ≫ p₁ ≫ (G.innerIso g).hom`,

and a linear equivalence `T : ρ₁ ≃ₗ[ℂ] ρ₂` with `T (ρ₁ m x) = ρ₂ (φ(m)) (T x)` for all `m : rationalPoints M₁` and `x : ρ₁`, where `φ(m) = rationalPoints.map φ.hom m`. Supercuspidality of `ρᵢ` means: for every actual rational parabolic `p' : P' ⟶ Mᵢ` of `Mᵢ` with rational Levi `l'`, matching radical `r'` and `hmul'`, `¬ IsIso p'` implies `Subsingleton ((jacquetFunctor p' l' r' …).obj ρᵢ)`.

## Interfaces

- `leviJacquetFunctor` is the published normalized Jacquet functor `r_P^G`, valued in smooth representations of `M(F)` with the canonical topology and the same carrier universe `v`.
- `SmoothRep.IsSubquotient` and `SmoothRep.IsIrreducible` are the published smooth-representation predicates.
- `G.innerIso g` is conjugation by `g`. The conclusion says that `φ` realizes `m ↦ g m g⁻¹` from `M₁` onto `M₂`, so `g M₁ g⁻¹ = M₂`, and that `ρ₁ ≅ ρ₂ ∘ φ`, i.e. `ρ₂ ≅ ρ₁^g`. The same encoding is used in `LeviSupercuspidalInductionAssociationStatement` and the published `TemperedIrreducibleDiscreteSeriesUniquenessStatement`.
- Supercuspidality is as in the published `MaximalLeviSupercuspidalReducibilityStatement`, following Renard's definition (VI.2.1, printed p.137 / PDF p.143).

## Faithfulness notes

- **Composition factors.** The source says that `ρ_i` is a composition factor of `r_{P_i}^G π`. That representation has finite length (VI.6.4; the represented form is `LeviJacquetFiniteLengthStatement`), and its composition factors are exactly its irreducible subquotients, up to isomorphism, by the Jordan–Hölder theorem. The statement uses irreducible subquotients, which does not presuppose finite length.
- **Arbitrary parabolics.** The Lemma is stated for arbitrary parabolics, and so is the statement.
- The carriers of `π`, `ρ₁` and `ρ₂` share the universe `v`, since `ρᵢ` is a subquotient of `r_{Pᵢ}^G π`, which has the carrier universe of `π`.

## Remaining obligations

The proof is a separate obligation. The source uses VI.6.4 and Corollary VI.6.1 (finite length and admissibility of `r_{P_i}^G π`), Lemma VI.3.6 (by which each `ρ_i` is a quotient of `r_{P_i}^G π`), Frobenius reciprocity, and the Theorem of VI.5.4. The represented forms are `LeviJacquetFiniteLengthStatement`, the published `ArbitraryParabolicJacquetAdmissibilityStatement`, the published `LeviFrobeniusReciprocityStatement` and `LeviSupercuspidalInductionAssociationStatement`. Lemma VI.3.6 is not stated for represented parabolics.

## Provenance

This is a derived statement of the Lemma of VI.7.1 for the represented-parabolic interface. The functors are the published `leviJacquetFunctor` and `jacquetFunctor`, and conjugation is the published `GroupScheme.innerIso`.
