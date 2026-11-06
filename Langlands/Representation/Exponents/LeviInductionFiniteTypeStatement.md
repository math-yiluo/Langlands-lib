# Normalized parabolic induction preserves finite type

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviInductionFiniteTypeStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviInductionFiniteTypeStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.7.5 "Noethérianité de M(G)", Theorem, printed p.187 / PDF p.193, with the announcement in the opening paragraph of VI.7.5 on printed p.186 / PDF p.192. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Theorem says: let `P = MN` be a parabolic subgroup of `G`; then the functor `i_P^G` preserves representations of finite type.

This is a source statement for the represented-parabolic interface. "Finite type" is finite generation over the group algebra, as in the published VI.1.3 statement `LeviJacquetFiniteTypeStatement`. The Proposition of VI.7.5 (`M(G)` is Noetherian) is the separate statement `SmoothRepNoetherianCategoryStatement` in this namespace.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`, every rational Levi `l : M ⟶ P` with `hl : IsRationalLeviSubgroup l`, and every matching geometric unipotent radical `r : U ⟶ P` with `hr : LeviSubgroup.IsGeometricUnipotentRadical r` and `hmul : IsIso (subgroupMultiplication l r)`.

For these data it installs on `rationalPoints M` the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl` from the published Levi-point interface `ArbitraryParabolicLeviPoints`.

Then, for every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` with an arbitrary carrier universe `v`, it asserts that

`Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) ρ.representation.asModule`

implies

`Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj ρ).representation.asModule`.

## The objects

- Finite type. A smooth representation is of finite type when finitely many vectors generate it as a representation. This is finite generation of the carrier as a module over the group algebra (`MonoidAlgebra`), through Mathlib's `Representation.asModule`. The published `Langlands.SmoothRep.renardFiniteType_iff` (module `Langlands.Representation.Category.RenardFinitenessProof`) proves that this agrees with Renard's categorical finite type `Langlands.Renard.IsFiniteTypeObject` of Appendix A.I.3 in the category of smooth representations.
- `leviInductionFunctor p l r hp hr hl hmul` is the published normalized induction `i_P^G`. It pulls a representation of `M(F)` back along the inverse of `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)` and applies the published induction `inductionFunctor` from the Levi image `pointImage (l ≫ p)` to `G(F)`. It sends carriers in universe `v` to carriers in universe `max u v`.

## Faithfulness notes

- The source states the Theorem for every parabolic `P = MN` and reduces to standard ones in its proof. The statement quantifies over every actual rational parabolic with a rational Levi and a matching radical, not only standard ones.
- No admissibility, finite length or irreducibility of `ρ` is assumed.
- The source proof shows more: `i_P^G(ρ)` is a Noetherian object. This is not stated separately. Given this statement, it follows from `SmoothRepNoetherianCategoryStatement` for `G` and the bridge `renardFiniteType_iff`.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `M(F)` are derived from them, not assumed.

## Remaining obligations

The proof is a separate obligation. The source argument uses:

- the Proposition of VI.7.5 (`SmoothRepNoetherianCategoryStatement`) for `M` and for `G`;
- for supercuspidal `ρ`, Proposition VI.5.3: only the standard `Q = LU` with `L` conjugate to `M` contribute to `R(i_P^G ρ)`, and for these `r_Q^G i_P^G ρ` has a filtration whose successive quotients are the `w·ρ`, `w ∈ W(L,M)/W_L`; together with faithfulness and exactness of the functor `R` of VI.7.2;
- in general, the embedding of the Lemma of VI.7.2 of `ρ` into a finite direct sum of inductions `i_{P'}^M ρ_{M'}` of supercuspidal representations from the standard parabolics `P' = M'N'` of `M`, exactness of `i_P^G`, and the transitivity of induction (VI.1.4).

Related published statements, none of which is asserted here: `LeviJacquetInductionVanishingStatement` (VI.5.3 (i)) and `LeviJacquetFiniteTypeStatement` (VI.1.3, finite type of `r_P^G`) in this namespace; and, on the standard rational-point family rather than the represented-parabolic interface, `Langlands.Aubert.General.RationalPointFamily.RationalCuspidalInducedEmbeddingStatement` (an existential consequence of the I/R embedding of VI.7.2).

## Provenance

This is a source statement of the Theorem of VI.7.5 for the represented-parabolic interface. Finite type is finite generation over the group algebra, as in the published VI.1.3 statement; the published bridge `renardFiniteType_iff` identifies it with Renard's categorical finite type.
