# Exactness of normalized parabolic induction and restriction

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviParabolicFunctorsExactStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviParabolicFunctorsExactStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The formalized result is the exactness part of the Proposition of VI.1.2 (printed p.136 / PDF p.142), in translation:

> The functors `i_P^G : M(M) → M(G)` and `r_P^G : M(G) → M(M)` are exact. The first is right adjoint to the second.

Here `P = MN` is any parabolic subgroup of `G`. The normalized functors are defined in (VI.1.2.1) and (VI.1.2.2) (printed p.135 / PDF p.141): `i_P^G(τ, E) = Ind_P^G(τ ⊗ δ_P^{-1/2}, E)` and `r_P^G(π, V) = (π_N ⊗ δ_P^{1/2}, V_N)`. The source proof (printed p.136) derives the proposition from the Theorem of VI.1.1 (printed p.135 / PDF p.141), the same result for unnormalized induction and the unnormalized Jacquet functor `j_N`, and notes that the two normalizations cancel (Remark III.1.15, 3). The adjunction part is the separate statement `LeviFrobeniusReciprocityStatement`.

This is a **derived** formulation, because the functors are the published normalized functors of the represented-parabolic interface, transported to representations of `M(F)` (see "The objects"), and exactness is stated as preservation of actual short exact sequences (see "Exactness"). The unnormalized Theorem of VI.1.1 is not stated separately.

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
- `leviJacquetFunctor p l r hp hr hl hmul` is the published transport of normalized Jacquet restriction `r_P^G`. It applies the published `jacquetFunctor`, which is `normalizedJacquetFunctor` for the radical image `pointImage (r ≫ p)` and the Levi image `pointImage (l ≫ p)`. It then pulls back along `leviPointsEquiv p l hp hl`. Its carrier is the actual quotient of coinvariants `V_N`. A Levi point `m` acts on the class `Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x` of `x` by `δ(m)^{-1/2}` times the class of `π(m) x`. The carrier universe is unchanged.

### Normalizations

Renard's modulus `δ_P` is the inverse of the usual modulus, as his remark after (VI.1.2.2) (printed p.136 / PDF p.142) and his modulus convention of II.3.7 explain. The published twists use the usual Haar modulus `δ`. Hence Renard's `δ_P^{-1/2}` in (VI.1.2.1) is the published `δ^{1/2}`, and Renard's `δ_P^{1/2}` in (VI.1.2.2) is the published `δ^{-1/2}`. With this dictionary, the published functors are exactly Renard's `i_P^G` and `r_P^G`; in particular a function `f` in `i_P^G σ` satisfies `f(x g) = δ(x)^{1/2} σ(e⁻¹(proj x)) f(g)` for `x` in the parabolic image, with `proj` the Levi projection and `e = leviPointsEquiv p l hp hl`, which is (VI.1.2.3).

## Exactness

The statement (universes `u`, `v`) is a conjunction:

1. for all smooth representations `A`, `B`, `C` of `M(F)` with carriers in universe `v`, and morphisms `f : A ⟶ B`, `g : B ⟶ C`, if `SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g)` holds, then the same holds for the images of `f` and `g` under `leviInductionFunctor p l r hp hr hl hmul`;
2. the same for smooth representations of `G(F)` and `leviJacquetFunctor p l r hp hr hl hmul`.

`SmoothRep.IsShortExact f g` says that `f` is injective, `g` is surjective and the range of `f` equals the kernel of `g`, that is, `0 → A → B → C → 0` is exact. Both functors are additive, so preserving short exact sequences is the source's exactness.

## Faithfulness notes

- The proposition is stated for every parabolic `P = MN`. The statement quantifies over every actual rational parabolic with a rational Levi and a matching radical, not only standard ones. No root presentation, minimal parabolic or Iwahori decomposition is assumed.
- No admissibility, finite length, finite type or irreducibility is assumed for any representation.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `M(F)` are derived from them, not assumed.
- The two exactness clauses use one carrier universe `v` for all three representations of each sequence, so the induced sequence lies in universe `max u v`.

## Remaining obligations

The proof is a separate obligation, and nothing is asserted here about how it is discharged. A natural route through the published Library is as follows. The published `Langlands.Aubert.General.jacquetFunctor_map_isShortExact` (module `Langlands.Representation.Aubert.General.AlternatingOperator`) needs `Jacquet.Localization.IsLimitOfCompactSubgroups` for the radical image. The published `Langlands.Aubert.General.normalizedInductionFunctor_map_isShortExact` in the same module needs `T2Space`, `CompactOpenCofinal` for `G(F)`, closedness of the parabolic image and continuity of the Levi projection. Each of these must be established for the actual rational points. Pull-back along a topological group isomorphism preserves short exactness, because it does not change the underlying linear maps.

## Provenance

This is a derived statement of the exactness part of the Proposition of VI.1.2 for the represented-parabolic interface. The source's derivation from the exactness in the Theorem of VI.1.1 is a proof route and is not represented. The normalized functors and the transport between `M(F)` and the Levi image are the published `leviInductionFunctor`, `leviJacquetFunctor` and `leviPointsEquiv`.
