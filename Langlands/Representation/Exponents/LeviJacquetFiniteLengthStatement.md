# Normalized parabolic restriction preserves finite length

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviJacquetFiniteLengthStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviJacquetFiniteLengthStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.6.4, printed p.179 / PDF p.185. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The subsection is titled "`r_P^G` préserve les représentations de longueur finie" and says, in translation: this is a consequence of Howe's theorem VI.6.3, of Theorem VI.1.3 and of Corollary VI.6.1. The introduction of VI.6 (printed pp.175–176 / PDF pp.181–182) states the same assertion: `r_P^G` preserves finite length.

This is a **derived** formulation, because the functor is the published normalized Jacquet functor `leviJacquetFunctor` of the represented-parabolic interface. Otherwise the statement follows the source.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`, every rational Levi `l : M ⟶ P` with `hl`, and every matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`. It installs on `rationalPoints M` the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`, and asserts

`SmoothRep.PreservesFiniteLength (leviJacquetFunctor.{u, v} p l r hp hr hl hmul)`.

## Interfaces

- `leviJacquetFunctor.{u, v} p l r …` is the published normalized Jacquet functor `r_P^G`, from smooth representations of `G(F)` to smooth representations of `M(F)`, both with carriers in `Type v`.
- `SmoothRep.PreservesFiniteLength` and `SmoothRep.HasFiniteLength` are as in `LeviInductionFiniteLengthStatement`: finite composition length over the group algebra.
- The published `Langlands.Aubert.General.DynamicJacquetFiniteLengthStatement` (`Aubert/General/PrerequisiteStatements`) asserts the same preservation for the parabolics `P(χ)` of cocharacters. This statement covers every actual rational parabolic with a rational Levi and a matching radical.

## Remaining obligations

The proof is a separate obligation. The source combines Howe's theorem VI.6.3 (finite length is equivalent to finite type and admissibility), Theorem VI.1.3 (`r_P^G` preserves finite type) and Corollary VI.6.1 (`r_P^G` preserves admissibility). The represented forms of the last two are the published `LeviJacquetFiniteTypeStatement` and `ArbitraryParabolicJacquetAdmissibilityStatement`, with proof tasks `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b` and `56206cc7-3e1e-4fae-840d-f5e8ccffd8ed`. The implication of Howe's theorem used here (finitely generated and admissible implies finite length) is the published `Langlands.SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement`, stated for the identity-test rational-point group `RationalPoint F G.X`; a proof must apply it to `M(F)` with its canonical topology. The converse direction, also needed (finite length of `π` gives finite type and admissibility), is part of the same theorem VI.6.3.

## Provenance

This is a derived statement of VI.6.4 for the represented-parabolic interface. The functor is the published `leviJacquetFunctor`; finite length is the published `SmoothRep.HasFiniteLength`, through `SmoothRep.PreservesFiniteLength`.
