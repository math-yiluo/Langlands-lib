# Frobenius reciprocity for normalized parabolic induction

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviFrobeniusReciprocityStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviFrobeniusReciprocityStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The formalized result is the adjunction part of the Proposition of VI.1.2 (printed p.136 / PDF p.142), in translation:

> The functors `i_P^G : M(M) → M(G)` and `r_P^G : M(G) → M(M)` are exact. The first is right adjoint to the second.

Here `P = MN` is any parabolic subgroup of `G`. The normalized functors are defined in (VI.1.2.1) and (VI.1.2.2) (printed p.135 / PDF p.141): `i_P^G(τ, E) = Ind_P^G(τ ⊗ δ_P^{-1/2}, E)` and `r_P^G(π, V) = (π_N ⊗ δ_P^{1/2}, V_N)`. The source proof (printed p.136) derives the proposition from the Theorem of VI.1.1 (printed p.135 / PDF p.141), the same result for unnormalized induction and the unnormalized Jacquet functor `j_N`, and notes that the two normalizations cancel (Remark III.1.15, 3). The exactness part is the separate statement `LeviParabolicFunctorsExactStatement`.

This is a **derived** formulation in two respects. The adjunction is stated as an explicit bijection of intertwiner spaces, given by evaluation at the identity (see "The adjunction"). The functors are the published normalized functors of the represented-parabolic interface, transported to representations of `M(F)` (see "The objects"). The unnormalized Theorem of VI.1.1 is not stated separately.

## Common data

The statement quantifies over the following data:

- a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`.

It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`. It assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology, as the other statements of this interface do.

It then quantifies over the following parabolic data:

- every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`;
- every rational Levi `l : M ⟶ P` with `hl : IsRationalLeviSubgroup l`;
- every matching geometric unipotent radical `r : U ⟶ P`, with `hr : LeviSubgroup.IsGeometricUnipotentRadical r` and `hmul : IsIso (subgroupMultiplication l r)`.

For these data it installs on `rationalPoints M`

- the affine instance `hl.isConnectedReductive.isAffineHom`;
- the canonical topology `leviPointTopology l hl`;
- local compactness and the nonarchimedean-group property, from `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`.

The categories `M(G)` and `M(M)` of the source are the categories `SmoothRep ℂ (rationalPoints G)` and `SmoothRep ℂ (rationalPoints M)` of smooth complex representations.

## The objects

- `leviInductionFunctor p l r hp hr hl hmul` is the published transport of normalized parabolic induction `i_P^G` to representations of `M(F)`. It pulls a representation of `M(F)` back along the inverse of the published isomorphism `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)`. It then applies the published `inductionFunctor`, which is `normalizedInductionFunctor` for the decomposition `isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul` of the parabolic image `pointImage p`. A carrier in universe `v` is sent to a carrier in universe `max u v`.
- `inducingRepresentation (isSemidirectDecomposition_pointImage …) (isClosed_pointImage_comp …) σ'` is the representation `x ↦ δ(x)^{1/2} σ'(proj x)` of the parabolic image. Here `σ'` is the pull-back of `σ`, `proj` is the Levi projection of the decomposition, and `δ^{1/2}` is the positive square root of the published Haar modulus `HaarModulus.closedHalfCharacter` of conjugation on the radical image. The space of `i_P^G σ` consists of smooth functions `f` with `f(x g) = δ(x)^{1/2} σ'(proj x) f(g)`, and `Induction.eval (pointImage p) _ f 1` is the value `f(1)`.
- `leviJacquetFunctor p l r hp hr hl hmul` is the published transport of normalized Jacquet restriction `r_P^G`. It applies the published `jacquetFunctor`, which is `normalizedJacquetFunctor` for the radical image `pointImage (r ≫ p)` and the Levi image `pointImage (l ≫ p)`. It then pulls back along `leviPointsEquiv p l hp hl`. Its carrier is the actual quotient of coinvariants `V_N`. A Levi point `m` acts on the class `Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x` of `x` by `δ(m)^{-1/2}` times the class of `π(m) x`. The carrier universe is unchanged.

### Normalizations

Renard's modulus `δ_P` is the inverse of the usual modulus, as his remark after (VI.1.2.2) (printed p.136 / PDF p.142) and his modulus convention of II.3.7 explain. The published twists use the usual Haar modulus `δ`. Hence Renard's `δ_P^{-1/2}` in (VI.1.2.1) is the published `δ^{1/2}`, and Renard's `δ_P^{1/2}` in (VI.1.2.2) is the published `δ^{-1/2}`. With this dictionary, the published functors are exactly Renard's `i_P^G` and `r_P^G`, and the transformation law above is (VI.1.2.3).

## The adjunction

The statement (universes `u`, `v`, `w`) asserts the following. Let `π : SmoothRep.{0, u, w} ℂ (rationalPoints G)` and `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` be arbitrary; their carrier universes `w` and `v` are independent. Then there is a `ℂ`-linear equivalence

`e : Hom_G(π, i_P^G σ) ≃ₗ[ℂ] Hom_M(r_P^G π, σ)`

between the spaces of intertwining maps (`Representation.IntertwiningMap`) such that, for every intertwiner `F : π → i_P^G σ` and every `x` in the carrier of `π`,

`e F [x] = (F x)(1)`.

Here `[x]` is the class `Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x`, and `(F x)(1)` is `Induction.eval (pointImage p) (inducingRepresentation …) (F x) 1`.

This is the adjunction "`i_P^G` is right adjoint to `r_P^G`" in explicit form. The classes `[x]` exhaust the coinvariant quotient, so the formula determines `e`. Naturality in `π` and `σ` is not stated as a separate clause. It follows from the formula by a direct computation, which is not carried out here. For an intertwiner `φ : π' → π`, both sides of naturality send `F` to the map `[x'] ↦ (F (φ x'))(1)`. For an intertwiner `ψ : σ → σ'`, the induced map acts by composition with `ψ` on values, so both sides give `[x] ↦ ψ((F x)(1))`. The same evaluation formula is the published `FirstAdjointness.equiv_mk` for the abstract normalized functors.

## Faithfulness notes

- The proposition is stated for every parabolic `P = MN`. The statement quantifies over every actual rational parabolic with a rational Levi and a matching radical, not only standard ones. No root presentation, minimal parabolic or Iwahori decomposition is assumed.
- No admissibility, finite length, finite type or irreducibility is assumed for any representation.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `M(F)` are derived from them, not assumed.
- The unimodularity of the radical `N(F)` is not assumed. It is part of what a proof must supply.

## Remaining obligations

The proof is a separate obligation, and nothing is asserted here about how it is discharged. A natural route through the published Library is as follows. Apply the published `Langlands.Aubert.General.FirstAdjointness.equiv` to the decomposition of the parabolic image. Its unimodularity hypothesis `IsUnimodularModulus (pointImage (r ≫ p)) _` is proved by the published `Langlands.Plancherel.parabolicRadical_isUnimodular` from a compatible `ParabolicRootPresentation`. Existence of such a presentation for an arbitrary actual parabolic is a separate open structural obligation. A proof that avoids it, for example from the fact that `N(F)` is a union of compact open subgroups, would also do. Then transport across `leviPointsEquiv`, which identifies intertwiners of pulled-back representations.

## Provenance

This is a derived statement of the adjunction part of the Proposition of VI.1.2 for the represented-parabolic interface. The adjunction is stated as the explicit evaluation-at-identity bijection, which determines the adjunction and implies its naturality. The source's derivation from the unnormalized Theorem of VI.1.1 is a proof route and is not represented. The normalized functors and the transport between `M(F)` and the Levi image are the published `leviInductionFunctor`, `leviJacquetFunctor` and `leviPointsEquiv`.
