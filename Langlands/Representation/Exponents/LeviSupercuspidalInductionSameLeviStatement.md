# Inductions of a supercuspidal representation along parabolics with the same Levi

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviSupercuspidalInductionSameLeviStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviSupercuspidalInductionSameLeviStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.5.4, Corollary, printed p.175 / PDF p.181, with its proof on the same page. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Corollary says: let `(ρ, W)` be an irreducible supercuspidal representation of a Levi subgroup `M` of `G`.

1. Let `P` and `Q` be two parabolic subgroups of `G` with Levi factor `M`. Then the Jordan–Hölder series of `i_P^G ρ` and `i_Q^G ρ` are equivalent.
2. There is always a nonzero intertwining operator between `i_P^G ρ` and `i_Q^G ρ`.
3. Let `P ∈ P(M)` and let `(π, V)` be an irreducible subquotient of `i_P^G ρ`. Then there is `Q ∈ P(M)` such that `(π, V)` is a subrepresentation of `i_Q^G(ρ, W)`.

Here `P(M)` is the set of parabolic subgroups of `G` with Levi factor `M`.

This is a **derived** formulation, because the functors are the published normalized functors of the represented-parabolic interface, supercuspidality is written out as the vanishing of normalized Jacquet modules, a parabolic with Levi factor `M` is an actual rational parabolic triple with the same Levi embedding `M → G`, and point 2 is stated for each ordered pair (see "Faithfulness notes").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over an actual rational parabolic triple `p : P ⟶ G`, `l : M ⟶ P`, `r : N ⟶ P` with `hp`, `hl`, `hr`, `hmul`, and installs on `rationalPoints M` the affine instance, the canonical topology `leviPointTopology l hl` and the derived instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`.

For every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` that is irreducible (`ρ.IsIrreducible`) and supercuspidal, it asserts the conjunction of:

- **points 1 and 2:** for every actual rational parabolic triple `q : Q ⟶ G`, `lQ : M ⟶ Q`, `rQ : U ⟶ Q` with `hq`, `hlQ`, `hrQ`, `hmulQ` and `lQ ≫ q = l ≫ p`,
  - `HaveSameJordanHolderFactors (SmoothRep.toRep.obj (i_P^G ρ)) (SmoothRep.toRep.obj (i_Q^G ρ))`, and
  - there are an intertwiner `f : i_P^G ρ ⟶ i_Q^G ρ` and a vector `x` with `SmoothRep.hom f x ≠ 0`;
- **point 3:** for every `σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` with `σ.IsIrreducible` and `SmoothRep.IsSubquotient σ (i_P^G ρ)`, there are an actual rational parabolic triple `(q, lQ, rQ)` as above with `lQ ≫ q = l ≫ p` and an intertwiner `f : σ ⟶ i_Q^G ρ` with `Function.Injective (SmoothRep.hom f)`.

Here `i_P^G ρ = (leviInductionFunctor p l r hp hr hl hmul).obj ρ` and `i_Q^G ρ = (leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj ρ`. Supercuspidality of `ρ` means: for every actual rational parabolic `p₁ : P₁ ⟶ M` of `M` with rational Levi `l₁`, matching radical `r₁` and `hmul₁`, `¬ IsIso p₁` implies `Subsingleton ((jacquetFunctor p₁ l₁ r₁ …).obj ρ)`.

## Interfaces

- `leviInductionFunctor` is the published normalized parabolic induction. For `Q`, the representation `ρ` of `M(F)` carries the canonical topology `leviPointTopology l hl`, which depends only on `M`, so the same `ρ` is induced along `P` and along `Q`.
- `HaveSameJordanHolderFactors` is Worker 14's published predicate of `Filtration.ObjectDefinitions`: composition series of the same length whose graded quotients are isomorphic after a permutation. It is applied to the underlying representations.
- `SmoothRep.IsSubquotient`, `SmoothRep.IsIrreducible` and `SmoothRep.hom` are the published smooth-representation interfaces.
- Supercuspidality is as in the published `MaximalLeviSupercuspidalReducibilityStatement`, following Renard's definition (VI.2.1, printed p.137 / PDF p.143).

## Faithfulness notes

- **Parabolics with Levi factor `M`.** `P` and `Q` have Levi factor `M` as subgroups of `G`. The statement takes a single Levi group scheme `M` with Levi maps `l : M ⟶ P` and `lQ : M ⟶ Q` and requires `lQ ≫ q = l ≫ p`: the two embeddings of `M` into `G` agree. Every actual rational parabolic with a rational Levi, a matching radical and this Levi embedding is allowed, without standardness.
- **Point 2.** The source asserts a nonzero intertwiner "between" the two inductions without fixing a direction. The statement asserts a nonzero intertwiner `i_P^G ρ → i_Q^G ρ` for every ordered pair `(P, Q)`, so both directions are covered.
- **Point 3.** A subrepresentation up to isomorphism is an injective intertwiner, as in the published `SmoothRep.IsSubrepresentation`. The parabolic `Q` is an actual rational parabolic triple whose Levi map has the same composite `M → G`. The source obtains it as a `G(F)`-conjugate of the parabolic given by Corollary VI.2.1. A proof has to realize that conjugate as actual group-scheme data.
- `ρ` is irreducible and supercuspidal, with no further assumption.

## Remaining obligations

The proof is a separate obligation. The source derives points 1 and 2 from the Theorem of VI.5.4, applied with `ρ' = ρ` and the trivially associated cuspidal data. Its represented form, without the numerical bounds, is `LeviSupercuspidalInductionAssociationStatement`. Point 3 uses Corollary VI.2.1 and the Theorem. Corollary VI.2.1 is published, with its proof, as `Langlands.Aubert.General.RationalPointFamily.RationalCuspidalEmbeddingStatement` for standard parabolics of the identity-test rational-point group. A represented form of it is not stated.

## Provenance

This is a derived statement of the Corollary of VI.5.4 for the represented-parabolic interface. The functors are the published `leviInductionFunctor` and `jacquetFunctor`, and Jordan–Hölder equivalence is Worker 14's published object-filtration predicate.
