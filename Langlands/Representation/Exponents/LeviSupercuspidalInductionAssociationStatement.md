# Induction from supercuspidal representations and cuspidal data

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviSupercuspidalInductionAssociationStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviSupercuspidalInductionAssociationStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.5.4, Theorem, printed pp.173–174 / PDF pp.179–180, with its proof on printed pp.174–175 / PDF pp.180–181. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Theorem says: let `P = MN` be a parabolic subgroup of `G`, `(ρ, W)` an irreducible supercuspidal representation of `M` and `(π, V) = i_P^G(ρ, W)`. Then `π` has finite length, at most `l(M)`. Moreover, if `P' = M'N'` is another parabolic subgroup of `G`, `(ρ', W')` an irreducible supercuspidal representation of `M'` and `π' = i_{P'}^G ρ'`, the following conditions are equivalent:

1. there is `g ∈ G` with `g M g⁻¹ = M'` and `ρ^g = ρ'`, i.e. the cuspidal data `(M, (ρ, W))` and `(M', (ρ', W'))` are associated;
2. `Hom_G(π, π') ≠ 0`;
3. the Jordan–Hölder series of `π'` and `π` are equivalent;
4. the Jordan–Hölder series of `π'` and `π` have at least one common element.

Finally, for standard `P` and `P'`, `dim Hom_G(π, π') ≤ |W_M \ W(ρ, ρ')|`. Cuspidal data and their association are defined in VI.5.2 (printed p.172 / PDF p.178).

This is a **derived partial** formulation. It states the finiteness of the length and the equivalence of the four conditions, for arbitrary actual parabolics. It does not state the bound `l(M)` or the bound on `dim Hom_G(π, π')`, which need the Weyl-group sets `W(∗, M)` and `W(ρ, ρ')` of V.4 for actual groups (see "Scope").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over two actual rational parabolic triples:

- `P = MN`: `p : P ⟶ G`, `l : M ⟶ P`, `r : N ⟶ P` with `hp`, `hl`, `hr`, `hmul`;
- `P' = M'N'`: `p' : P' ⟶ G`, `l' : M' ⟶ P'`, `r' : N' ⟶ P'` with `hp'`, `hl'`, `hr'`, `hmul'`.

On `rationalPoints M` and `rationalPoints M'` it installs the affine instances, the canonical topologies `leviPointTopology l hl` and `leviPointTopology l' hl'`, and the derived local-compactness and nonarchimedean-group instances from `ArbitraryParabolicLeviPoints`. For every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` and `ρ' : SmoothRep.{0, u, v} ℂ (rationalPoints M')` that are irreducible (`IsIrreducible`) and supercuspidal, it asserts, with `π = (leviInductionFunctor p l r …).obj ρ` and `π' = (leviInductionFunctor p' l' r' …).obj ρ'`:

- **finite length:** `∃ n, HasCompositionSeriesLength (SmoothRep.toRep.obj π) n`;
- **equivalences:** `List.TFAE` of the four conditions
  1. there are `g : rationalPoints G` and `φ : M ≅ M'` with `φ.hom ≫ l' ≫ p' = l ≫ p ≫ (G.innerIso g).hom`, and a linear equivalence `T : ρ ≃ₗ[ℂ] ρ'` with `T (ρ m x) = ρ' (φ(m)) (T x)` for all `m : rationalPoints M` and `x : ρ`, where `φ(m) = rationalPoints.map φ.hom m`;
  2. there are an intertwiner `f : π ⟶ π'` and a vector `x` with `SmoothRep.hom f x ≠ 0`;
  3. `HaveSameJordanHolderFactors (SmoothRep.toRep.obj π) (SmoothRep.toRep.obj π')`;
  4. there is `σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` with `σ.IsIrreducible`, `SmoothRep.IsSubquotient σ π` and `SmoothRep.IsSubquotient σ π'`.

Supercuspidality of `ρ` means: for every actual rational parabolic `p₁ : P₁ ⟶ M` of `M` with rational Levi `l₁`, matching radical `r₁` and `hmul₁`, `¬ IsIso p₁` implies `Subsingleton ((jacquetFunctor p₁ l₁ r₁ …).obj ρ)`; the same for `ρ'` and `M'`.

## Interfaces

- `leviInductionFunctor` is the published normalized parabolic induction; it raises the carrier universe from `v` to `max u v`, so `σ` has carriers in `Type (max u v)`.
- `HasCompositionSeriesLength A n` and `HaveSameJordanHolderFactors A B` are the published object-filtration predicates of `Langlands.Representation.Filtration.ObjectDefinitions` (Worker 14). The first asserts an actual filtration of `A` with `n` irreducible graded quotients. The second asserts composition series of `A` and `B` of the same length whose graded quotients are isomorphic after a permutation, that is, equal Jordan–Hölder factors with multiplicities. They are applied to the underlying representations `SmoothRep.toRep.obj π`. Irreducibility there is `Representation.IsIrreducible`, which is also the published `SmoothRep.IsIrreducible`.
- `SmoothRep.IsSubquotient` is the published subquotient relation; `SmoothRep.hom f` is the underlying linear map of an intertwiner.
- `G.innerIso g` is conjugation by `g`. Condition 1 says that `φ` realizes `m ↦ g m g⁻¹` from `M` onto `M'`, so `g M g⁻¹ = M'`, and that `T` is an isomorphism `ρ ≅ ρ' ∘ φ`. Since `ρ^g(g m g⁻¹) = ρ(m)`, this is `ρ^g ≅ ρ'`. The same encoding is used in the published `TemperedIrreducibleDiscreteSeriesUniquenessStatement`.
- Supercuspidality is as in the published `MaximalLeviSupercuspidalReducibilityStatement`, following Renard's definition (VI.2.1, printed p.137 / PDF p.143).

## Scope

- **Bounds not stated.** The length bound `l(M) = |W_M \ W(∗, M)|` and the bound `dim Hom_G(π, π') ≤ |W_M \ W(ρ, ρ')|` for standard parabolics are not part of the statement. They need the sets `W(L, M)` of V.4.3–V.4.6 for actual groups, which the represented-parabolic interface does not provide.
- **Condition 4.** The source's "at least one common element of the Jordan–Hölder series" is stated as a common irreducible subquotient. For representations of finite length the two are equivalent by the Jordan–Hölder theorem, and finite length is part of the conclusion.
- **Arbitrary parabolics.** The source proves the Theorem after conjugating `P` and `P'` to standard parabolics. The statement quantifies over all actual rational parabolics with rational Levis and matching radicals.
- The published `Langlands.Aubert.General.RationalPointFamily.RationalSupercuspidalInductionFiniteLengthStatement` states the finite-length assertion for standard parabolics of the identity-test rational-point group. This statement covers every represented parabolic and adds the four equivalences.

## Remaining obligations

The proof is a separate obligation. The source route uses Corollary VI.2.1 (every irreducible representation has a nonzero supercuspidal Jacquet module), Proposition VI.5.3, exactness of the Jacquet functors, Frobenius reciprocity, Lemma VI.3.6, the maximal-Levi case `l(M) = 2`, and the factorization of Weyl elements into elementary ones ([5], Lemma 2.17). For represented parabolics, assertions (i) and (ii) of VI.5.3 are the statements `LeviJacquetInductionVanishingStatement` and `LeviJacquetInductionNoSupercuspidalStatement`; assertion (iii) is not stated. Corollary VI.2.1 is the published `Langlands.Aubert.General.RationalPointFamily.RationalCuspidalEmbeddingStatement` for standard parabolics of the identity-test rational-point group, with its published proof; a represented form is not stated.

## Provenance

This is a derived partial statement of the Theorem of VI.5.4 for the represented-parabolic interface. The functors are the published `leviInductionFunctor` and `jacquetFunctor`; finite length and Jordan–Hölder equivalence are Worker 14's published object-filtration predicates; association of cuspidal data uses the published `GroupScheme.innerIso`.
