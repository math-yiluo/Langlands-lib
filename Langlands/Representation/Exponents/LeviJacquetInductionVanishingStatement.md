# Jacquet modules of supercuspidal inductions vanish without conjugate Levis

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviJacquetInductionVanishingStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviJacquetInductionVanishingStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.5.3, Proposition, assertion (i), printed p.173 / PDF p.179, with its proof on the same page. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Proposition says: let `P = MN` and `Q = LU` be parabolic subgroups of `G`, `(ρ, W)` a supercuspidal representation of `M`, and put `τ = r_Q^G i_P^G ρ`. Then (i) if `L` has no Levi subgroup conjugate to `M` in `G`, then `τ = 0`. Assertion (ii) is the separate statement `LeviJacquetInductionNoSupercuspidalStatement`; assertion (iii) is not stated.

This is a **derived** formulation, because the functors are the published normalized functors of the represented-parabolic interface, supercuspidality is written out as the vanishing of normalized Jacquet modules, and conjugacy of Levi subgroups is expressed through isomorphisms of group schemes (see "Conjugate Levi subgroups").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over two actual rational parabolic triples:

- `P = MN`: `p : P ⟶ G`, `l : M ⟶ P`, `r : N ⟶ P` with `hp`, `hl`, `hr`, `hmul`;
- `Q = LU`: `q : Q ⟶ G`, `lQ : L ⟶ Q`, `rQ : U ⟶ Q` with `hq`, `hlQ`, `hrQ`, `hmulQ`.

It assumes that there are no group schemes `P''`, `M''`, maps `p'' : P'' ⟶ L` and `l'' : M'' ⟶ P''` with `IsParabolicSubgroup p''` and `IsRationalLeviSubgroup l''`, element `g : rationalPoints G` and isomorphism `φ : M ≅ M''` with

`φ.hom ≫ l'' ≫ p'' ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso g).hom`.

On `rationalPoints M` it installs `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`. For every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` that is supercuspidal, it asserts

`Subsingleton ((jacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))`,

that is, `r_Q^G i_P^G ρ = 0`. Supercuspidality of `ρ` means: for every actual rational parabolic `p' : P' ⟶ M` of `M` with rational Levi `l'`, matching radical `r'` and `hmul'`, `¬ IsIso p'` implies `Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)`.

## Conjugate Levi subgroups

A Levi subgroup of `L` is a Levi factor `M''` of a parabolic subgroup `P''` of `L`; this includes `L` itself, the Levi factor of the parabolic `L`. The hypothesis quantifies over every actual rational parabolic `p'' : P'' ⟶ L` and every rational Levi `l'' : M'' ⟶ P''`. The rational-Levi predicate already supplies a matching radical, so none is quantified. `G.innerIso g` is conjugation by `g`, which acts by `x ↦ g x g⁻¹` on points. The equation says that `φ` followed by the inclusion `M'' → G` is the inclusion `M → G` followed by conjugation by `g`, so `g M g⁻¹ = M''` as subgroups of `G`, with `φ` the induced isomorphism. Since the inclusions are monomorphisms, such a `φ` exists exactly when the two image subgroup functors are conjugate by `g`.

## Interfaces

- `leviInductionFunctor p l r …` is the published normalized parabolic induction `i_P^G`.
- `jacquetFunctor q lQ rQ …` is the published normalized Jacquet functor along `Q`, valued in representations of the Levi image `pointImage (lQ ≫ q)`. The pullback to `L(F)` by the Levi-point isomorphism, `leviJacquetFunctor`, has the same carrier, so the vanishing conclusion does not depend on this choice.
- Supercuspidality is as in the published `MaximalLeviSupercuspidalReducibilityStatement`: Renard's definition (VI.2.1, printed p.137 / PDF p.143) is the vanishing of `r_P` for every proper parabolic, and twisting by the modulus does not change vanishing.

## Faithfulness notes

- The Proposition is stated for arbitrary parabolics `P` and `Q`, and so is the statement. No standardness is assumed.
- `ρ` is supercuspidal but not necessarily irreducible, admissible or of finite length, as in the source.

## Remaining obligations

The proof is a separate obligation. The source derives (i) from the geometric lemma VI.5.1: the graded pieces of `r_Q^G i_P^G ρ` are `i^L_{Q'} ∘ ι ∘ r^M_{P'} ρ`, and each `r^M_{P'} ρ` vanishes unless `P' = M`, in which case `M` is a Levi subgroup of `w·L`. The represented geometric lemma is the published `RepresentedGeometricLemmaStatement`, whose proof is task `c060fb34-b423-4ac5-8448-788ac7627913`.

## Provenance

This is a derived statement of assertion (i) of the Proposition of VI.5.3 for the represented-parabolic interface. The functors are the published `leviInductionFunctor` and `jacquetFunctor`, and conjugation is the published `GroupScheme.innerIso`.
