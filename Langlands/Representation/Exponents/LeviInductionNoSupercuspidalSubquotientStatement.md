# No supercuspidal subquotients in proper parabolic induction

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviInductionNoSupercuspidalSubquotientStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviInductionNoSupercuspidalSubquotientStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.5.2, Lemma, printed p.173 / PDF p.179, with its proof on the same page. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Lemma says: let `P = MN` be a proper parabolic subgroup of `G` and `(ρ, W)` a smooth representation of `M`, and put `(π, V) = i_P^G(ρ, W)`. Then no irreducible subquotient of `(π, V)` is supercuspidal.

Renard's definition of supercuspidality (VI.2.1, printed p.137 / PDF p.143) is the vanishing of `r_P V` for every proper parabolic subgroup `P` of the group.

This is a **derived** formulation, because the functors are the published normalized functors of the represented-parabolic interface and supercuspidality is written out as the vanishing of normalized Jacquet modules for every proper actual parabolic (see "Supercuspidality").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`, every rational Levi `l : M ⟶ P` with `hl`, and every matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`, and assumes `¬ IsIso p`: the parabolic is proper.

On `rationalPoints M` it installs `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`. For every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` and every `σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` with `σ.IsIrreducible` and `SmoothRep.IsSubquotient σ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)`, it asserts that `σ` is not supercuspidal. That is, it is not the case that for every actual rational parabolic `p' : P' ⟶ G` with rational Levi `l'`, matching radical `r'` and `hmul'`, `¬ IsIso p'` implies `Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj σ)`.

## Interfaces

- `leviInductionFunctor p l r …` is the published normalized parabolic induction `i_P^G`. It sends carriers in `Type v` to carriers in `Type (max u v)`, so `σ` is taken with carriers in `Type (max u v)`.
- `SmoothRep.IsSubquotient σ π` is the published subquotient relation: there are a subrepresentation `S` of `π`, a subrepresentation `T` of `S`, and an isomorphism of `σ` with the actual quotient `S/T`.
- `σ.IsIrreducible` is the published irreducibility predicate for smooth representations.
- `jacquetFunctor p' l' r' …` is the published normalized Jacquet functor, valued in representations of the Levi image `pointImage (l' ≫ p')`.

## Supercuspidality

Renard defines `π` to be supercuspidal when `r_P π = 0` for every proper parabolic subgroup `P`. The statement uses the normalized Jacquet module for every proper actual rational parabolic with a rational Levi and a matching radical, as in the published `MaximalLeviSupercuspidalReducibilityStatement`. Twisting by the modulus does not change vanishing, and by Remark 1 of VI.2.1 standard parabolics would suffice. A zero carrier is written `Subsingleton`.

## Faithfulness notes

- The Lemma is stated for every proper parabolic and every smooth `ρ`. The statement quantifies over every actual proper rational parabolic and every smooth `ρ`, without admissibility, finite length or irreducibility.
- Only irreducible subquotients are considered, as in the source. The zero representation satisfies the vanishing condition trivially, and irreducibility excludes it.

## Remaining obligations

The proof is a separate obligation. The source proves the Lemma from the decomposition of VI.3.5 into a supercuspidal part and its complement and from Frobenius reciprocity: `Hom_G(π_sc, π) = Hom_M(r_P π_sc, ρ) = 0`. The represented Frobenius reciprocity is the published `LeviFrobeniusReciprocityStatement`, whose proof is task `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b`. The decomposition of VI.3.5 for actual reductive groups is not asserted here.

## Provenance

This is a derived statement of the Lemma of VI.5.2 for the represented-parabolic interface. The functors are the published `leviInductionFunctor` and `jacquetFunctor`; subquotients and irreducibility are the published smooth-representation predicates.
