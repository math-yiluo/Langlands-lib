# Uniqueness of the discrete-series datum of an irreducible tempered representation

Author: Worker 6. Module `Langlands.Representation.Exponents.TemperedIrreducibleDiscreteSeriesUniquenessStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `TemperedIrreducibleDiscreteSeriesUniquenessStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.6, Theorem, second assertion, printed p.231 / PDF p.237, with its proof on printed pp.231–232 / PDF pp.237–238. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The first assertion of the theorem says that an irreducible `(π, V)` is tempered if and only if it is a subrepresentation of `i_P^G(σ, E)` for some standard `P = MN` and some irreducible `(σ, E)` of `M` that is square-integrable modulo the center (companion statement unit `TemperedIrreducibleDiscreteSeriesStatement`). The second assertion says: if `(P_1 = M_1 N_1, (σ_1, E_1))` and `(P_2 = M_2 N_2, (σ_2, E_2))` are two pairs with this property, there is `g ∈ G` such that `g M_1 g^{-1} = M_2` and `σ_1^g ≃ σ_2`.

This is a **derived** formulation: the parabolics are arbitrary actual rational parabolics, and conjugation of Levi subgroups is expressed through an isomorphism of group schemes. See "Faithfulness notes".

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`.

Levi data, discrete representations and embeddings are as in the companion unit. A Levi datum is an actual rational parabolic `p`, rational Levi `l : M ⟶ P` and matching radical `r` with `hmul`. Its Levi points `rationalPoints M` carry `leviPointTopology l hl` and the derived local-compactness and nonarchimedean instances. A discrete `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` is irreducible and satisfies `IsSquareIntegrableModCenter σ.representation haar` for every Haar measure on `rationalPoints M ⧸ Subgroup.center (rationalPoints M)`. An embedding is an injective `π.representation.IntertwiningMap ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation`.

The statement asserts: for every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` with `π.IsIrreducible`, every Levi datum `(P₁, M₁, U₁, p₁, l₁, r₁, hp₁, hl₁, hr₁, hmul₁)` with a discrete `σ₁` and an embedding of `π` into the induction of `σ₁`, and every second Levi datum `(P₂, M₂, …)` with a discrete `σ₂` and an embedding of `π` into the induction of `σ₂`, there are `g : rationalPoints G` and an isomorphism `φ : M₁ ≅ M₂` of group schemes with

`φ.hom ≫ l₂ ≫ p₂ = l₁ ≫ p₁ ≫ (G.innerIso g).hom`,

and a linear equivalence `T : σ₁ ≃ₗ[ℂ] σ₂` such that `T (σ₁.representation m x) = σ₂.representation (rationalPoints.map φ.hom m) (T x)` for all `m : rationalPoints M₁` and `x : σ₁`.

## The objects

- `G.innerIso g` is the inner automorphism of the group scheme `G` given by `g`. By the published `rationalPoints_map_innerIso` it acts on points as `x ↦ g x g⁻¹`. The equation for `φ` therefore says that conjugation by `g` carries the image of `M₁` in `G` onto that of `M₂`, and that `φ` is the induced isomorphism. This is Renard's `g M₁ g⁻¹ = M₂`.
- Renard's `σ₁^g` is the representation `m₂ ↦ σ₁(g⁻¹ m₂ g)` of `M₂`. With `m₂ = φ(m)`, the condition on `T` says exactly that `T` intertwines `σ₁^g` and `σ₂`, i.e. `σ₁^g ≃ σ₂`. It is stated with the rational-point map `rationalPoints.map φ.hom` and a linear equivalence of carriers, so no topology on the transported representation is needed.
- The other objects (`leviInductionFunctor`, `IsSquareIntegrableModCenter`, `SmoothRep.IsIrreducible`) are as described in the companion unit.

## Faithfulness notes

- **All parabolics.** The source's pairs have standard parabolics, through the first assertion. The statement allows arbitrary actual rational parabolics. This is the expected extension: every parabolic is `G(F)`-conjugate to a standard one, and conjugating `(P, σ)` by `h` replaces `M` by `h M h⁻¹`, `σ` by `σ^h` and `i_P^G σ` by an isomorphic representation. The reduction to standard pairs is part of the proof obligation.
- **Levi subgroups as group schemes.** A Levi subgroup is a group scheme `M` with the closed immersion `l ≫ p` into `G`, not a literal subgroup. The source's `g M₁ g⁻¹ = M₂` is therefore an isomorphism `φ` compatible with conjugation by `g`. Since closed immersions are monomorphisms, `φ` is determined by `g` when it exists.
- **No extra hypotheses.** No temperedness, admissibility, finite length or central character of `π` is assumed beyond irreducibility and the two embeddings. Temperedness of `π` follows from the first assertion.

## Remaining obligations

The proof is a separate obligation. The source route uses unitarity of square-integrable representations and of their normalized inductions (IV.3.2), finite length and hence semisimplicity of `i_P^G σ`, the tempered Frobenius reciprocity of VII.2.4, exactness of `r_P^G`, the tempered geometric lemma VII.2.5, Lemma VII.2.4, Frobenius reciprocity, and the Weyl-group representatives `W_{M₂,M₁}` of V.4.6. It also needs the structural inputs these use for actual reductive groups and the reduction to standard pairs.

## Provenance

This is a derived statement of the second assertion of the Theorem of VII.2.6 for the represented-parabolic interface. Square-integrability is the published IV.3.2 predicate applied to `M(F)`, and induction is the published `leviInductionFunctor`. Allowing arbitrary parabolics and expressing conjugation through `G.innerIso g` and an isomorphism of Levi group schemes are formalization choices explained above.
