# Jacquet modules of contragredients

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviJacquetContragredientStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviJacquetContragredientStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.9.6, second Theorem, printed p.201 / PDF p.207. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation: let `P = MN` be a parabolic subgroup of `G` and `P̄ = M N̄` the opposite parabolic; then for every smooth representation `(π, V)` of `G`,

`r_{P̄}^G π̃ = (r_P^G π)~`. (VI.9.6.2)

The source's proof that the two Theorems are equivalent ends with "l'existence d'un isomorphisme naturel `r_{P̄}^G π̃ ≃ (r_P^G π)~`" (printed p.202 / PDF p.208). Accordingly, (VI.9.6.2) is read as a natural isomorphism in `π`. The source then proves this Theorem equivalent to the first Theorem of VI.9.6, second adjointness, which is the separate statement `LeviSecondAdjointnessStatement`.

This is a **derived** formulation, for three reasons. The functors are the published normalized functors of the represented-parabolic interface. The opposite parabolic is described by explicit data and two compatibility hypotheses, as in `LeviSecondAdjointnessStatement`. The contragredient is the published smooth contragredient functor.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over two actual rational parabolic triples with the same Levi group scheme `M`:

- `P = MN`: `p : P ⟶ G`, `m : M ⟶ P`, `n : N ⟶ P` with `hp`, `hm`, `hn`, `hmul`;
- `P̄ = M N̄`: `pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar` with `hpbar`, `hmbar`, `hnbar`, `hmulbar`.

It assumes `mbar ≫ pbar = m ≫ p` and `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`: the triples have the same Levi embedding, and `P(F) ∩ P̄(F) = M(F)`. The Markdown of `LeviSecondAdjointnessStatement` explains why these hypotheses characterize the opposite parabolic. On `rationalPoints M` it installs `hm.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology m hm`, and the instances `leviPoints_locallyCompactSpace p m hp hm` and `leviPoints_nonarchimedeanGroup p m hp hm`. It then asserts

`Nonempty (SmoothRep.contragredientFunctor ⋙ leviJacquetFunctor pbar mbar nbar … ≅ (leviJacquetFunctor p m n …).op ⋙ SmoothRep.contragredientFunctor)`,

an isomorphism of functors `(SmoothRep.{0, u, v} ℂ (rationalPoints G))ᵒᵖ ⥤ SmoothRep.{0, u, v} ℂ (rationalPoints M)`, for an arbitrary carrier universe `v`.

## The functors

- `SmoothRep.contragredientFunctor` is the published contravariant smooth contragredient `π ↦ π̃`. It takes smooth linear functionals with the inverse-transpose action, and a morphism acts by precomposition. With coefficients `ℂ` in `Type`, it preserves the carrier universe `v`, since `max 0 v = v`.
- `leviJacquetFunctor p m n …` and `leviJacquetFunctor pbar mbar nbar …` are the published normalized Jacquet functors `r_P^G` and `r_{P̄}^G`. Each takes coinvariants for its radical image, twists by the inverse square root of the usual Haar modulus (Renard's `δ^{1/2}` in (VI.1.2.2)), and pulls back to `M(F)` along its `leviPointsEquiv`. Both land in representations of `M(F)` with the same canonical topology `leviPointTopology`.
- The left side is `π ↦ r_{P̄}^G(π̃)`. The right side is `π ↦ (r_P^G π)~`.

## Faithfulness notes

- The Theorem is stated for every parabolic `P = MN` and every smooth `π`, with no admissibility. The statement quantifies over every actual rational parabolic with any actual opposite in the sense above, and over every smooth representation of `G(F)`.
- The isomorphism is natural in `π`, as an isomorphism of functors. No explicit formula is asserted. The source constructs it from the pairing (VI.9.6.4), whose normalization involves contracting elements of the split component. The statement asserts only existence.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `M(F)` are derived from them, not assumed.

## Remaining obligations

The proof is a separate obligation. The source proves this Theorem through an `M`-equivariant nondegenerate pairing `⟨·,·⟩_P : r_P^G(V) × r_{P̄}^G(Ṽ) → ℂ` with the normalization (VI.9.6.4) for contracting elements `t ∈ C_A^{++}` (the Proposition after the second Theorem). That pairing is built from the generalized Jacquet lemma VI.9.1 and VI.9.2–VI.9.3. A proof needs Iwahori decompositions with respect to `P` and `P̄` and contracting elements of the split component for the actual rational points. None of this is asserted here.

## Provenance

This is a derived statement of the second Theorem of VI.9.6 for the represented-parabolic interface. The functors are the published `leviJacquetFunctor` and `SmoothRep.contragredientFunctor`. The opposite parabolic is given by an actual rational parabolic triple with the same Levi whose rational points meet those of `P` exactly in the Levi image. The source's equality of functors is read as a natural isomorphism.
