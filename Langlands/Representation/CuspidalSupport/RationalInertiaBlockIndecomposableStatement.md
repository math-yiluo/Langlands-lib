# Renard VI.4.5, Corollary: the inertia block M(G)[π] is indecomposable

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locator is the last Corollary of VI.4.5 and its proof, printed p.160 / PDF p.166. The notation 𝓜 = ∏ᵢ 𝓜ᵢ for a decomposition of a category is defined in A.IX, printed p.268 / PDF p.274, and the center of a category in A.X, printed p.269 / PDF p.275. The proof uses the Lemma and Corollary of VI.4.3 (A is a domain), printed pp.154–155 / PDF pp.160–161, and the isomorphism between Z and the center Z[π] of M(G)[π] earlier on p.160. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

(π,V) is an irreducible supercuspidal representation of G and M(G)[π] is the full subcategory of smooth representations all of whose irreducible subquotients lie in the inertia class [π] (VI.3.3).

**Corollary.** The category M(G)[π] is indecomposable.

**Proof (source).** When an abelian category splits as a direct sum of two categories, the projections onto the two factors are idempotents in the center of the category. Since Z is a domain (by the Lemma of VI.4.3), it contains no nontrivial idempotent.

A.IX writes 𝓜 = ∏_{i ∈ I} 𝓜ᵢ, for a family of full subcategories 𝓜ᵢ, when every object M is a direct sum ⊕ᵢ Mᵢ with Mᵢ ∈ 𝓜ᵢ and Hom(Xᵢ, Xⱼ) = 0 for i ≠ j and all objects Xᵢ ∈ 𝓜ᵢ, Xⱼ ∈ 𝓜ⱼ.

## Lean content

Write H = G(F), with its canonical rational-point topology.

**`RationalInertiaBlockIndecomposableStatement`.** The premises are those of the VI.4 statements without ρ, with the maximal split torus renamed S:

- an arbitrary connected reductive G over an arbitrary nonarchimedean local field F, a maximal split torus inclusion i : S → G and a generic cocharacter ν;
- explicit `StandardCocharacterStatement`, relative-root-system and standard-unipotent-closedness premises, from which the finite simple-root index set and the actual semidirect decompositions are derived;
- local compactness, the nonarchimedean group property and Hausdorffness of H;
- π an irreducible actual smooth complex representation of H with carrier in `Type uV`, cuspidal in the sense of the published `Aubert.General.IsCuspidal` (every proper standard normalized Jacquet module vanishes).

Let B be the published full category `RationalInertiaBlock G (rationalInertiaBaseLift G π)`, Renard's M(G)[π]. The conclusion: for every family P : `Bool → ObjectProperty B` with `Renard.IsCategoryDecomposition P`, there is b : Bool such that every object X of B with P b X is a zero object (`IsZero X`).

## Correspondence and conventions

**Decompositions.** The published `Langlands.Renard.IsCategoryDecomposition P` is A.IX's B = ∏ᵢ P i: every object is the vertex of an actual coproduct cofan with one component in each P i, and every morphism between objects of distinct P i is zero. A decomposition into two full subcategories is the case of the index type `Bool`, as in the published `RationalInertiaDecompositionStatement` (VI.3.3). The library's definition does not need, and the statement does not assume, the Grothendieck and AB6 hypotheses under which A.IX introduces the notation.

**Indecomposable.** Renard does not define the word. The Lean statement reads it as: in every decomposition B = P false × P true in the sense of A.IX, one factor is trivial, meaning that all its objects are zero (it may be empty). The full subcategories P b are arbitrary object properties, not assumed closed under isomorphism, so "trivial" is stated on objects rather than by asking P b to be empty or to equal the zero objects.

**Relation with the source proof.** Given such a decomposition, the projections onto the components form an idempotent element of the center of B, as in the source proof; the factor P true is trivial exactly when this idempotent is 0, and P false is trivial exactly when it is 1. The center of B is a domain by the separate statements `RationalSummandBlockCenterStatement` (isomorphism with the center of R = End Π) and `RationalNormKernelEndDomainStatement` (R is a domain, Corollary (i) of VI.4.3). This explains the statement and is not part of it.

**The universe lift.** The block is formed from the published `rationalInertiaBaseLift G π`, which applies the fully faithful `SmoothRep.universeLiftFunctor` to π and has carrier in `Type (max uF uV)`, as in the VI.4.1 statements, where the progenerator Π lives. π has carrier in `Type uV`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

**Cuspidality.** Renard's π is supercuspidal. As in the VI.4.1 statements and Worker 1758's `RationalUniversalSmallProgeneratorStatement`, cuspidality is measured by the vanishing of every proper standard normalized Jacquet module. Comparing this with cuspidality along all proper rational parabolics is a separate obligation.

There is no splitness, characteristic-zero, admissibility, compactness or finite-dimensionality premise on π. The statement does not assume that B is abelian.

## Provenance

The statement is the source Corollary, with "indecomposable" made precise through Renard's notation of A.IX for two factors, as explained above.

## Scope

This module defines a Prop-valued target only. It does not prove the statement. The center of the block is described by the separate statements `RationalSummandBlockCenterStatement` and `RationalInertiaBlockCenterEvaluationStatement`.
