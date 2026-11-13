# A basis of the endomorphisms of the induced progenerator

Author: Worker 5226. This is an internal construction with supporting results. It was derived for the third conjunct (the free-module conjunct) of `InducedProgeneratorEndFreeStatement`, the first Lemma of Renard VI.10.4 (printed pp.209–210 / PDF pp.215–216). Reference: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The main definition `inducedProgeneratorEndBasis` and the theorem `inducedProgeneratorEnd_expansion` take two hypotheses that are not proved in this file: `Π_D` is projective, and `Π_D` is supercuspidal. See "Hypotheses not proved here" below.

## Relation to Renard

Renard's Lemma says that `R_Ω = End_G(i_P Π_D)` is a free right module of rank `|W(D)|` over `R_D = End_M(Π_D)`. His proof (printed p.210 / PDF p.216) has three steps.

1. Bernstein's second adjointness, followed by the block projection `r_D`, gives `R_Ω ≃ Hom_M(Π_D, r_D i_P Π_D)` (VI.10.4.3). This is an isomorphism of right `R_D`-modules.
2. By (V.4.3.3), VI.5.3(iii) and the definition of `W(D)`, `r_D i_P Π_D` has a filtration with successive quotients `w·Π_D`, `w ∈ W(D)`.
3. All `w·Π_D` are projective, so the filtration splits. Renard then asserts that `w·Π_D ≃ Π_D` for `w ∈ W(D)`, so `R_Ω ≃ R_D^{|W(D)|}`.

This file reaches the same conclusion by a different route, devised by the author. It is not a formalization of Renard's argument.

1. It uses the first adjunction `r_P ⊣ i_P` (`leviFirstAdjunction`) instead of second adjointness. This identifies `R_Ω` with `Hom_M(r_P i_P Π_D, Π_D)`: the Jacquet functor is taken along `P`, not `P̄`, and the Hom arguments are reversed. The transport is `inducedEndBasis` (`Langlands/Representation/Filtration/InducedEndBasis.lean`).
2. It does not use the block projection `r_D`. It filters the whole functor `r_P ∘ i_P` by the geometric lemma, with one step for every double coset in `P(F)\G(F)/P(F)`: `leviJacquetSupportFiltration`, with graded pieces from `representedGeometricLemmaSupportGraded_of_orbitComparison`. For the double cosets of `W(D)`, the representatives are chosen to be points of `W(D)` themselves.
3. At a point of `W(D)` the piece of `Π_D` is the pullback of `Π_D` along an automorphism of `M(F)`. That pullback is isomorphic to `Π_D` by `nonempty_pullback_rationalNormKernelSummandInduction_iso` (`NormKernelSummandPullback.lean`). This is Renard's assertion `w·Π_D ≃ Π_D`. The isomorphism is compatible with `End(Π_D)` by `fullPieceEquiv_naturality`.
4. At any other point, every map from the piece of `Π_D` to `Π_D` is zero. This replaces Renard's block projection. There are two cases:
   - if the datum is not full, the piece is zero because `Π_D` is supercuspidal (`subsingleton_pieceFunctor_obj`);
   - if it is full, a nonzero map would put the point in `W(D)`, by `exists_pullback_iso_twist_of_hom_ne_zero`.
5. Every graded projection has a section, because every piece of `Π_D` is either a pullback of the projective `Π_D` or zero. This corresponds to Renard's splitting.

`homVanishingBasis`, used through `inducedEndBasis`, then gives a basis indexed by the steps in `W(D)`. The basis is reindexed by `W(D)`.

## Setting

- `k` is a nonarchimedean local field.
- `G` is a group scheme over `k` that is connected reductive (`hG`). Its rational points carry `RationalPointFamily.pointTopology` and are assumed locally compact and nonarchimedean.
- `P = MN` is an actual rational parabolic of `G`, given by `p l r hp hr hl hmul`. `M(F)` carries `leviPointTopology l hl`.
- `i_P = leviInductionFunctor.{u, max u v} p l r hp hr hl hmul` and `r_P = leviJacquetFunctor.{u, max u v} …`.
- `π : SmoothRep.{0, u, v} ℂ M(F)` is irreducible, `ρ₀` is an irreducible smooth representation of `⁰M = rationalCommonNormKernel M`, and `j : ρ₀ ⟶ π|_{⁰M}` is injective.
- `Π_D = CuspidalSupport.rationalNormKernelSummandInduction M ρ₀ = c-ind_{⁰M}^{M(F)} ρ₀`. It is a `SmoothRep.{0, u, max u v}`, so `i_P` is used at universe `max u v` and no universe lift is needed.
- `(End Π_D)ᵐᵒᵖ` acts on `i_P Π_D ⟶ i_P Π_D` through `RepFunctorFiltration.endPrecompModule`: `op a • x = i_P(a) ≫ x`. In the usual notation this is `x ∘ i_P(a)`, the right `R_D`-module structure of Renard.
- A self-intersection datum at `z ∈ G(F)` is a `GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z`. Its source parabolic is `P' = M ∩ zPz⁻¹` (`D.p' : P' ⟶ M`), and its `pieceFunctor` is `i^M_{Q'} ∘ e^* ∘ r^M_{P'}`. The datum is *full* when `D.p'` is an isomorphism, that is `M ∩ zPz⁻¹ = M`.

## Declarations

### General lemmas

- `SmoothRep.exists_section_of_projective hZ f hf P iY`: let `f : Z ⟶ Y` be a surjection of representations with `Z` smooth, and `iY : Y ≅ toRep.obj P` with `P` a projective smooth representation. Then `f` has a section `σ` with `σ ≫ f = 𝟙 Y`. The proof lifts `f ≫ iY.hom` to an epimorphism `f'` of smooth representations, factors `𝟙 P` through it (`Projective.factorThru`), and transports back along `iY`.
- `RepFunctorFiltration.nonempty_inducedEndBasis_of_comp_eq adj T s X hsec θ S hθ hzero hΦ`: the conclusion of `inducedEndBasis` (as `Nonempty` of the basis), for a filtration `s` of a functor `Φ` and a proof `hΦ : Ind ⋙ Res ⋙ T = Φ`. The proof is `subst hΦ` and `inducedEndBasis`. It exists only for elaboration: `Φ` is fixed by `s` and the equation comes last, so the hypotheses are checked against `Φ` and not against the composite read off the adjunction. Checking them against that composite timed out.
- `RepFunctorFiltration.existsUnique_precomp_expansion_of_basis Φ X Z e B`: let `B` be a basis of `Φ.obj X ⟶ Z` over `(End X)ᵐᵒᵖ` (for `endPrecompModule`) indexed by `J`, with `e : J ≃ Fin m`. Then there are `b : Fin m → (Φ.obj X ⟶ Z)` such that every `x` is `∑ i, Φ.map (a i) ≫ b i` for exactly one `a : Fin m → (X ⟶ X)`. Here `b` is `B.reindex e`. Existence takes `a i = (b.equivFun x i).unop`; uniqueness applies `b.equivFun` (`Module.Basis.equivFun_symm_apply`).

### Self-intersection data (`section Datum`)

- `isIso_p'_of_normalizes D φ hφ`: let `φ : M ≅ M` satisfy `φ.hom ≫ l ≫ p = l ≫ p ≫ inn(z)`, that is `z` normalizes `M` through `φ`. Then `D.p'` is an isomorphism. The proof computes the range of `D.p'` as the preimage of `zPz⁻¹` in `M` (`SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf` with `D.parabolic_eq`). Every point `x` of `M` lies in it, through the point `x ≫ φ⁻¹ ≫ l` of `P`. Then `isIso_of_full_range` applies.
- `fullTargetConjugacy_hom_eq D φ hφ`: for a full datum, the conjugacy `M ≅ M` recovered by `D.fullTargetConjugacy (Iso.refl M)` is `φ`. Both satisfy the same equation, and `l ≫ p` is a monomorphism (a closed immersion).

### Pieces (`section Pieces`)

Here `σ` is any smooth representation `SmoothRep.{0, u, max u v} ℂ M(F)`, and `D` is a self-intersection datum at `z`. Write `e_D = D.fullTargetPointsEquiv (Iso.refl M) h` for a full datum (`h : IsIso D.p'`). It is the automorphism of `M(F)` recovered from `D`. `D.fullTargetPieceEquiv` identifies the piece of `σ` with `SmoothRep.pullback e_D σ`.

- `exists_section_of_iso_pieceFunctor_obj D σ hproj hsc hZ f hf iY`: for `σ` projective and supercuspidal, a surjection `f : Z ⟶ Y` from a smooth `Z` onto `Y ≅ D.pieceFunctor.obj σ` has a section. There are two cases:
  - if `D` is full, the piece is `pullback e_D σ`, which is projective because `SmoothRep.pullbackEquivalence e_D` is an equivalence; then `SmoothRep.exists_section_of_projective` applies;
  - otherwise the piece is zero (`subsingleton_pieceFunctor_obj`, from supercuspidality), so `Y` is zero and `0` is a section.
- `exists_bijective_of_pullback_iso D σ h ψ`: let `D` be full, and `ψ : pullback e_D σ ≅ σ`. Then there is `θ : D.pieceFunctor.obj σ ⟶ σ` such that `a ↦ D.pieceFunctor.map a ≫ θ` is a bijection `End(σ) → Hom(piece of σ, σ)`. Here `θ` is the piece isomorphism `iD` followed by `ψ`. The map is the composite of four bijections, by `fullPieceEquiv_naturality`:
  - `a ↦ (pullbackFunctor e_D).map a`, bijective because the pullback is an equivalence;
  - `b ↦ b ≫ ψ.hom`;
  - `SmoothRep.toRep.map`, bijective because `toRep` is fully faithful;
  - `c ↦ iD.hom ≫ c`.
- `eq_zero_of_pullback_hom_eq_zero D σ hsc hfull g`: let `σ` be supercuspidal, and suppose that, if `D` is full, every map `pullback e_D σ ⟶ σ` is zero. Then every `g : D.pieceFunctor.obj σ ⟶ σ` is zero. If `D` is full, `g` is transported to a map out of `pullback e_D σ`. Otherwise the piece is zero.
- `exists_bijective_of_witness`: the case `σ = Π_D` at a point of `W(D)`. Assume `φ : M ≅ M` with `φ.hom ≫ l ≫ p = l ≫ p ≫ inn(z)`, `e` the map of `φ` on rational points, and an iso `pullback e π ≅ π ⊗ χ` with `χ` unramified. Then the conclusion of `exists_bijective_of_pullback_iso` holds for `Π_D`. The proof:
  - `D` is full (`isIso_p'_of_normalizes`), and `e_D = e` (`fullTargetConjugacy_hom_eq`);
  - `e` preserves `⁰M` (`mem_rationalCommonNormKernel_mapIso_iff`);
  - `nonempty_pullback_rationalNormKernelSummandInduction_iso` gives `pullback e Π_D ≅ Π_D`;
  - `exists_bijective_of_pullback_iso` applies.
- `eq_zero_of_not_witness`: the case `σ = Π_D` at a point `z` not in `W(D)`, that is, no `φ, e, χ` as above exist for `z`. Assume `Π_D` supercuspidal. Then every map from the piece of `Π_D` to `Π_D` is zero. This is `eq_zero_of_pullback_hom_eq_zero`. For a full datum, a nonzero `f : pullback e_D Π_D ⟶ Π_D` would give, by `exists_pullback_iso_twist_of_hom_ne_zero`, an unramified `χ` with `pullback e_D π ≅ π ⊗ χ`. Together with `D.fullTargetConjugacy`, this would put `z` in `W(D)`.

### Assembly (`section Assembly`)

- `twistStabilizerDoubleCosets p l hp hl π`: the set of double cosets `P(F) w P(F)` of points `w ∈ G(F)` such that `w` normalizes `M` through some `φ : M ≅ M` (`φ.hom ≫ l ≫ p = l ≫ p ≫ inn(w)`) and `π ∘ φ` is an unramified twist of `π`. It is the same set-builder term as the set `W` of `InducedProgeneratorEndFreeStatement`, the actual-group form of Renard's `W(D)`.
- `nonempty_inducedEndBasis_of_witnesses hG p l r hp hr hl hmul σ hproj hsc W Q hW hQW hbij hzero`: a general form of the basis, for `σ` projective and supercuspidal. Let `W` be a set of double cosets and `Q` a property of points of `G(F)`. Assume:
  - `hW`: every coset of `W` contains a point satisfying `Q` that carries a self-intersection datum;
  - `hQW`: every point satisfying `Q` lies in a coset of `W`;
  - `hbij`: at every datum whose point satisfies `Q`, some `θ` makes `a ↦ D.pieceFunctor.map a ≫ θ` bijective;
  - `hzero`: at every datum whose point does not satisfy `Q`, all maps from the piece of `σ` to `σ` vanish.

  Then `End(i_P σ)` has a basis over `(End σ)ᵐᵒᵖ` indexed by `W`. The proof has five steps. It uses `set_option maxHeartbeats 800000`.
  1. `representedGeometricLemmaGeometry` gives finitely many double cosets, each with a representative carrying a datum. `closedSubgroupOrbitOrdering` orders them so that initial unions are open.
  2. Representatives are chosen by `choose`. On a coset of `W` it is a point satisfying `Q` from `hW`; on any other coset it is the representative from step 1. `classifiedRepresentatives` turns them into representatives of the ordering. For each step `i` this gives a datum `E i` at the inverse of the representative and the coset `ε i`.
  3. `F = leviJacquetSupportFiltration.{u, max u v}` is the geometric-lemma filtration of `r_P ∘ i_P`. `representedGeometricLemmaSupportGraded_of_orbitComparison` identifies its graded pieces with `(E i).pieceFunctor`.
  4. Let `S` be the set of steps whose coset lies in `W`. On `S`, `θ` comes from `hbij` composed with the graded iso. Off `S`, vanishing comes from `hzero`. Sections come from `exists_section_of_iso_pieceFunctor_obj`, using that `F.step` of a smooth representation is smooth.
  5. `nonempty_inducedEndBasis_of_comp_eq`, with `leviFirstAdjunction`, `T = SmoothRep.toRep` and the functor equation `rfl`, gives a basis indexed by `S`. It is reindexed by `S ≃ W`, `i ↦ ε i`.
- `nonempty_inducedProgeneratorEndBasis`: the case `σ = Π_D`, `W = twistStabilizerDoubleCosets p l hp hl π`, with `Q w` the defining condition of `W(D)` at `w`. It assumes `Projective Π_D` and `IsSupercuspidal Π_D`.
  - Every `w` satisfying `Q` carries a self-intersection datum. `ParabolicLeviTorus.exists_maximalSplitTorus_factor` gives a maximal split torus `t` of `G` inside `M`, and `geometricLemmaIntersectionDatumOfTorusFactors` builds the datum from `t` and `t ≫ φ⁻¹`. This uses `φ⁻¹ ≫ l ≫ p ≫ inn(w) = l ≫ p`.
  - `hbij` is `exists_bijective_of_witness`, and `hzero` is `eq_zero_of_not_witness`.
- `inducedProgeneratorEndBasis hG p l r hp hr hl hmul π hπ ρ₀ hρ₀ j hj hproj hsc`: **the main definition**. It is a `Module.Basis (twistStabilizerDoubleCosets p l hp hl π) (End Π_D)ᵐᵒᵖ (i_P Π_D ⟶ i_P Π_D)`, for the precomposition action above, chosen by `Classical.choice` from `nonempty_inducedProgeneratorEndBasis`. It is the Lean form of "the right `R_D`-module `R_Ω` is free with a basis indexed by `W(D)`".
- `inducedProgeneratorEnd_expansion`: under the same hypotheses, `W` is finite, and there are `b : Fin W.ncard → (i_P Π_D ⟶ i_P Π_D)` such that every `x` is uniquely `∑ i, i_P(a i) ≫ b i` with `a i ∈ End(Π_D)`. Its conclusion is the third conjunct of `InducedProgeneratorEndFreeStatement`, with the same `let` bindings, together with the finiteness conjunct.
  - Finiteness is `normalizerDoubleCosets_subset_finite`, because every coset of `W` comes from a normalizing point.
  - The expansion is `existsUnique_precomp_expansion_of_basis` applied to `inducedProgeneratorEndBasis`, with `e = (Finite.equivFin W).trans (finCongr (Nat.card_coe_set_eq _))`.

## Hypotheses not proved here

- `Projective Π_D`. The Library proves it as `rationalNormKernelSummandInduction_projective` (`RationalSummandSmallProgeneratorReduction.lean`), from compact smooth dual coefficients of `π|_{⁰M}`. For supercuspidal `π`, those coefficients come from `compactRestriction_of_isSupercuspidal` (Renard VI.2.1). That theorem assumes `JointSpecialCompactBasisExistenceStatement`, which is not yet proved.
- `IsSupercuspidal Π_D`. For supercuspidal `π` this is `isSupercuspidal_rationalNormKernelSummandInduction` (`RationalSummandInductionSupercuspidal.lean`).

This file does not assemble `InducedProgeneratorEndFreeStatement`. Its first and second conjuncts are `leviInductionEndEmbedding` and `normalizerDoubleCosets_subset_finite`. Its fourth conjunct follows from the third by `leviInducedEndCenterExpansion_of_endExpansion` (`NormKernelSummandCenterBasis.lean`).
