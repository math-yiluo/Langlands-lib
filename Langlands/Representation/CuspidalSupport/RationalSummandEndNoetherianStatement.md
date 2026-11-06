# Renard VI.4.4, Corollary: End(ind_{⁰G}^G ρ) is noetherian

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locator is the Corollary of VI.4.4 and its proof, printed p.159 / PDF p.165. Its proof uses the Theorem of VI.4.4 (printed pp.158–159 / PDF pp.164–165) and the Proposition of VI.4.4 (printed p.159 / PDF p.165). The setting is that of VI.4.1–VI.4.3, printed pp.149–155 / PDF pp.155–161. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard keeps the notation of VI.4.1–VI.4.3: (π,V) is an irreducible supercuspidal representation of G, (ρ,W) is an irreducible summand of the restriction of π to ⁰G, Π = ind_{⁰G}^G ρ, R = End_G(Π), and A = H(N,ρ) is the convolution algebra of VI.4.2–VI.4.3, isomorphic to R.

**Corollary.** The ℂ-algebra A is noetherian.

The proof says: the center Z of A is isomorphic to a Laurent polynomial algebra in several variables, hence noetherian; A is a finitely generated Z-module (by the Theorem of VI.4.4 it is free of rank m²); and one concludes by a standard result on finite algebras over noetherian commutative rings. Renard adds that M(G)[π] is therefore equivalent to the category of right modules over a noetherian algebra.

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology.

**`RationalSummandEndNoetherianStatement`.** The premises are exactly those of `RationalSummandSmallProgeneratorStatement`, the Proposition of VI.4.1, with the maximal split torus renamed S:

- an arbitrary connected reductive G over an arbitrary nonarchimedean local field F, a maximal split torus inclusion i : S → G and a generic cocharacter ν;
- explicit `StandardCocharacterStatement`, relative-root-system and standard-unipotent-closedness premises, from which the finite simple-root index set and the actual semidirect decompositions are derived;
- local compactness, the nonarchimedean group property and Hausdorffness of H;
- π an irreducible actual smooth complex representation of H with carrier in `Type uV`, cuspidal in the sense of the published `Aubert.General.IsCuspidal` (every proper standard normalized Jacquet module vanishes);
- ρ an irreducible actual smooth representation of H⁰ with carrier in `Type uV`, with an injective H⁰-equivariant linear map j : ρ → `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π`.

Let I be the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`. This is Renard's Π, the same object as `rationalNormKernelSummandInduction G ρ` in the VI.4.1 module; it is written out so that the module does not import that file. `End I` is its endomorphism ring in the category of smooth representations of H.

The conclusion is `IsNoetherianRing (End I) ∧ IsNoetherianRing (End I)ᵐᵒᵖ`.

## Correspondence and conventions

**Left and right.** Mathlib's `IsNoetherianRing R` says that R is noetherian as a left module over itself, that is, every ascending chain of left ideals stabilizes. Applied to the opposite ring it says the same for right ideals. Renard's A is not commutative in general, and his proof (a finitely generated module over a noetherian central subalgebra) gives both. The conjunction states that `End I` is left and right noetherian, which is how the statement reads Renard's "noetherian".

**R versus A.** Renard states the Corollary for A = H(N,ρ). The Lean statement is made for R = `End I`. The Proposition of VI.4.2, stated separately as `RationalNormKernelHeckeStatement`, identifies R with A as ℂ-algebras. Being left and right noetherian is preserved by ring isomorphisms, so the two forms say the same thing. The present statement does not import or use the VI.4.2 statement. Multiplication in `End I` is composition, α * β = β ≫ α; the conjunction is symmetric in left and right, so this convention does not affect the statement.

**Choice of ρ.** As in the VI.4.1 statements, Renard's ρ is an irreducible summand of Res π, and the Lean statement takes every irreducible ρ with an injective equivariant map into Res π. By VI.3.2 these are, up to isomorphism, the summands.

**Cuspidality.** Renard's π is supercuspidal. As in the VI.4.1 statements and Worker 1758's `RationalUniversalSmallProgeneratorStatement`, cuspidality is measured by the vanishing of every proper standard normalized Jacquet module. Comparing this with cuspidality along all proper rational parabolics is a separate obligation.

**Universes.** π and ρ have carriers in `Type uV`, and I has carrier in `Type (max uF uV)`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

There is no splitness, characteristic-zero, admissibility, compactness or finite-dimensionality premise on ρ or π.

## Provenance

The statement is kept in Renard's setting: an irreducible cuspidal π and an irreducible ρ embedded in Res π. Renard's proof goes through the Theorem and the Proposition of VI.4.4, which need that setting. The provenance is recorded as source.

## Scope

This module defines a Prop-valued target only. It does not prove the statement. The concluding remark that M(G)[π] is equivalent to the category of right modules over a noetherian algebra is not stated; it combines this Corollary with the equivalence of VI.4.1, stated separately as `RationalSummandHomEquivalenceStatement`. The Theorem of VI.4.4 is the separate module `RationalSummandEndCenterStatement`, and the Proposition of VI.4.4 is the separate module `RationalSummandCenterGroupAlgebraStatement`. The Lemma of VI.4.4 is not stated.
