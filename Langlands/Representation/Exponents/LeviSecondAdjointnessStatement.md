# Bernstein's second adjointness for represented parabolics

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviSecondAdjointnessStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviSecondAdjointnessStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.9.6, first Theorem, printed p.201 / PDF p.207. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation: let `P = MN` be a parabolic subgroup of `G` and `P̄ = M N̄` the opposite parabolic; then the functor `r_{P̄}^G` is right adjoint to `i_P^G`, that is, for every smooth `(π, V)` of `G` and every smooth `(τ, E)` of `M` there is a natural isomorphism

`Hom_G(i_P^G(τ, E), (π, V)) ≃ Hom_M((τ, E), r_{P̄}^G(π, V))`. (VI.9.6.1)

The source calls this Bernstein's second adjointness theorem. The second Theorem of VI.9.6, `r_{P̄}^G π̃ ≅ (r_P^G π)~`, is the separate statement `LeviJacquetContragredientStatement`. The source proves the two equivalent on printed pp.201–202 / PDF pp.207–208.

This is a **derived** formulation, for three reasons. The functors are the published normalized functors of the represented-parabolic interface. The opposite parabolic is described by explicit data and two compatibility hypotheses (see "The opposite parabolic"). The natural isomorphism is Mathlib's `Adjunction` on representations whose carriers lie in a universe containing that of the field (see "Universes").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over two actual rational parabolic triples with the same Levi group scheme `M`:

- `P = MN`: a parabolic `p : P ⟶ G` with `hp`, a rational Levi `m : M ⟶ P` with `hm`, and a matching geometric unipotent radical `n : N ⟶ P` with `hn` and `hmul`;
- `P̄ = M N̄`: a parabolic `pbar : Pbar ⟶ G` with `hpbar`, a rational Levi `mbar : M ⟶ Pbar` with `hmbar`, and a matching geometric unipotent radical `nbar : Nbar ⟶ Pbar` with `hnbar` and `hmulbar`.

It assumes `mbar ≫ pbar = m ≫ p` and `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`. It installs on `rationalPoints M` the affine instance `hm.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology m hm`, and the instances `leviPoints_locallyCompactSpace p m hp hm` and `leviPoints_nonarchimedeanGroup p m hp hm`. It then asserts

`Nonempty (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣ leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar)`.

## The opposite parabolic

Renard's `P̄` is the opposite parabolic of `P` relative to `M`: the parabolic with Levi `M` and `P ∩ P̄ = M`. The two hypotheses say this on rational points. The first says that `M` is a Levi of `P̄` with the same embedding in `G`. The second says that `P(F) ∩ P̄(F)` is the Levi image `M(F)`.

These hypotheses characterize the opposite parabolic. `P ∩ P̄'` is `M ⋉ (N ∩ P̄')` for any parabolic `P̄'` with Levi `M`. The group `N ∩ P̄'` is split unipotent, so it is trivial as soon as its rational points are, and then `P̄'` is the opposite. This argument explains the hypotheses; it is not part of the statement. The statement quantifies over every such pair, so it covers every parabolic with its opposite, provided the opposite is given as actual group-scheme data. Constructing that data is a structural question not addressed here.

The canonical topology `leviPointTopology` depends only on `M`, so the induced and restricted representations of `M(F)` carry the same topology.

## The functors

- `leviInductionFunctor p m n …` is the published normalized parabolic induction `i_P^G`. It pulls back along the inverse of `leviPointsEquiv p m hp hm` and applies the published `inductionFunctor` from the Levi image. The twist is the square root of the usual Haar modulus, which is Renard's `δ_P^{-1/2}` in (VI.1.2.1), because Renard's `δ_P` is the inverse of the usual modulus.
- `leviJacquetFunctor pbar mbar nbar …` is the published normalized Jacquet functor `r_{P̄}^G`. It takes coinvariants for the radical image `pointImage (nbar ≫ pbar)`, twists by the inverse square root of the usual modulus, and pulls back along `leviPointsEquiv pbar mbar hpbar hmbar`.
- `F ⊣ G'` is Mathlib's `Adjunction`. It gives bijections `Hom(F X, Y) ≃ Hom(X, G' Y)` natural in both variables, which is (VI.9.6.1). The `Nonempty` wrapper asserts existence of such an adjunction.

## Universes

The source does not consider universes. In Lean, `leviInductionFunctor.{u, w}` sends carriers in `Type w` to carriers in `Type (max u w)`, and `leviJacquetFunctor.{u, w}` preserves the carrier universe. Mathlib's `Adjunction` needs the two functors to go between the same two categories. The statement therefore takes `w = max u v` for an arbitrary `v`. Then both functors relate `SmoothRep.{0, u, max u v} ℂ (rationalPoints M)` and `SmoothRep.{0, u, max u v} ℂ (rationalPoints G)`, since `max u (max u v) = max u v`. So the adjunction is asserted for every carrier universe containing the universe `u` of the field. A representation with a smaller carrier can be lifted to such a universe with `ULift`.

## Faithfulness notes

- The Theorem is stated for every parabolic `P = MN`. The statement quantifies over every actual rational parabolic with a rational Levi and a matching radical, with any actual opposite in the sense above, not only standard ones.
- No admissibility, finite length or finite type is assumed for any representation. This generality is the point of the source's proof through the generalized Jacquet lemma VI.9.1.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `M(F)` are derived from them, not assumed.

## Remaining obligations

The proof is a separate obligation. The source derives (VI.9.6.1) from (VI.9.6.2) using the first adjunction (VI.1.2), the compatibility of normalized induction with contragredients (IV.2.1.2), Lemma I.4.2.1 and left exactness. It proves (VI.9.6.2) through an `M`-equivariant nondegenerate pairing `r_P^G(V) × r_{P̄}^G(Ṽ) → ℂ` (the Proposition after the second Theorem, (VI.9.6.4)). That pairing is built from the generalized Jacquet lemma VI.9.1 and its consequences VI.9.2–VI.9.3, which need Iwahori decompositions and contracting elements of the split component. None of this is asserted here.

## Provenance

This is a derived statement of the first Theorem of VI.9.6 for the represented-parabolic interface. The functors are the published `leviInductionFunctor` and `leviJacquetFunctor`. The opposite parabolic is given by an actual rational parabolic triple with the same Levi whose rational points meet those of `P` exactly in the Levi image. The natural isomorphism is a Mathlib adjunction on carriers in universe `max u v`.
