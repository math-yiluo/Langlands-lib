# Normalized parabolic induction preserves finite length

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviInductionFiniteLengthStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviInductionFiniteLengthStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.6.2, printed p.178 / PDF p.184. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The section opens, in translation: "We now show that the induction functor `i_P^G` preserves modules of finite length." Its Lemma says: let `P = MN` be a parabolic subgroup of `G` and `(τ, E)` an irreducible representation of `M`; then `i_P^G(τ, E)` has finite length. The introduction of VI.6 (printed pp.175–176 / PDF pp.181–182) lists the same assertion: `i_P^G` preserves finite length.

This is a **derived** formulation. The functor is the published normalized induction `leviInductionFunctor` of the represented-parabolic interface, and the statement is the preservation of finite length announced by the section, of which the Lemma is the irreducible case (see "Faithfulness notes").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`, every rational Levi `l : M ⟶ P` with `hl`, and every matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`. It installs on `rationalPoints M` the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`, and asserts

`SmoothRep.PreservesFiniteLength (leviInductionFunctor.{u, v} p l r hp hr hl hmul)`.

## Interfaces

- `leviInductionFunctor.{u, v} p l r …` is the published normalized parabolic induction `i_P^G`, from smooth representations of `M(F)` with carriers in `Type v` to smooth representations of `G(F)` with carriers in `Type (max u v)`. The carrier universe `v` is arbitrary.
- `SmoothRep.PreservesFiniteLength Φ` (`Smooth/FiniteLengthGrothendieckFunctor`) says that `Φ` sends every smooth representation with `HasFiniteLength` to one with `HasFiniteLength`. `SmoothRep.HasFiniteLength` is finite composition length of the carrier as a module over the group algebra, not finite dimension.
- The published `Langlands.Aubert.General.DynamicInductionFiniteLengthStatement` (`Aubert/General/PrerequisiteStatements`) asserts the same preservation for the parabolics `P(χ)` of cocharacters. This statement covers every actual rational parabolic with a rational Levi and a matching radical.

## Faithfulness notes

- The Lemma of VI.6.2 is the case of an irreducible `τ`; an irreducible representation has finite length 1. The statement asserts the preservation for every finite-length `τ`, which the opening sentence of VI.6.2 and the introduction of VI.6 announce and which follows from the Lemma by exactness of `i_P^G` (VI.1.2) and induction on the length. The statement therefore implies the Lemma.
- No admissibility is assumed. Every actual rational parabolic is allowed, not only standard ones.

## Remaining obligations

The proof is a separate obligation. The source proves the Lemma from the Theorem of VI.5.4 for supercuspidal `τ` and, for general irreducible `τ`, from Corollary VI.2.1, exactness of `i_P^G` and transitivity of induction. The represented forms of VI.5.4 and of exactness are `LeviSupercuspidalInductionAssociationStatement` and the published `LeviParabolicFunctorsExactStatement`. Transitivity of induction for represented parabolics is not stated; the published `DynamicNestedParabolicTransitivityStatement` covers dynamic parabolics.

## Provenance

This is a derived statement of VI.6.2 for the represented-parabolic interface. The functor is the published `leviInductionFunctor`; finite length is the published `SmoothRep.HasFiniteLength`, through `SmoothRep.PreservesFiniteLength`.
