# Renard VI.4.5, Proposition: the center of M(G)[π] is the algebra of functions on Irr(G)[π], acting by evaluation

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locator is the first Proposition of VI.4.5 and its proof, printed p.160 / PDF p.166. It uses the isomorphism Z ≃ Z[π] stated earlier on the same page, the Proposition of VI.4.4 (ψ_x and ℂ[T/⁰G] ≃ Z), printed p.159 / PDF p.165, (VI.4.4.5)–(VI.4.4.7) in the proof of the Theorem of VI.4.4, printed pp.158–159 / PDF pp.164–165, and the definition of T with the Remark of VI.4.4 (the algebra of functions on Irr(G)[π] is ℂ[T/⁰G]), printed pp.156–157 / PDF pp.162–163. The center of a category is defined in A.X, printed p.269 / PDF p.275. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

(π,V) is an irreducible supercuspidal representation of G, X(G) is the torus of unramified characters, X(G)(π) = {ω | π ⊗ ω ≃ π}, and T = ⋂_{ω ∈ X(G)(π)} ker ω, a subgroup of G containing ⁰G. By the Remark of VI.4.4, X(G)(π) consists of the ω trivial on T, the algebra of polynomial functions on the torus X(G)/X(G)(π) is ℂ[T/⁰G], and since X(G)/X(G)(π) is identified with Irr(G)[π] (Remarks VI.3.3, ω ↦ π ⊗ ω), the algebra of polynomial functions on Irr(G)[π] is ℂ[T/⁰G]. Under these identifications the class of t ∈ T is the function π ⊗ ω ↦ ω(t). Z[π] is the center of the category M(G)[π].

**Proposition.** Let z ∈ Z[π] and τ ∈ Irr(G)[π]. Interpret z as an element of the algebra of functions on the affine algebraic variety Irr(G)[π]. Then the evaluation of z at the point τ is the scalar z(τ) by which z acts on τ.

**Proof (source).** Let ω ∈ X(G) and x ∈ T. It suffices to treat z = z_{ψ_x}, where ψ_x is the element of Z of the Proposition of VI.4.4. By (VI.4.4.5), ψ_x acts on the simple right module Hom_{⁰G}(ρ, π ⊗ ω) by ω(x). Hence z_{ψ_x} acts on π ⊗ ω by ω(x).

The interpretation of z as a function is the composite of the isomorphism Z[π] ≃ Z of VI.4.5 (φ ↦ z_φ) and the isomorphism ℂ[T/⁰G] ≃ Z of the Proposition of VI.4.4 (class of g ↦ ψ_g).

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology.

**`RationalInertiaBlockCenterEvaluationStatement`.** The premises are those of the VI.4 statements without ρ, with the maximal split torus renamed S:

- an arbitrary connected reductive G over an arbitrary nonarchimedean local field F, a maximal split torus inclusion i : S → G and a generic cocharacter ν;
- explicit `StandardCocharacterStatement`, relative-root-system and standard-unipotent-closedness premises, from which the finite simple-root index set and the actual semidirect decompositions are derived;
- local compactness, the nonarchimedean group property and Hausdorffness of H;
- π an irreducible actual smooth complex representation of H with carrier in `Type uV`, cuspidal in the sense of the published `Aubert.General.IsCuspidal` (every proper standard normalized Jacquet module vanishes).

As in `RationalSummandEndCenterStatement`, T is the subgroup of H given by the infimum, over all ω in the published `unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)` with `Nonempty (rationalUnramifiedTwist G ω π ≅ π)`, of the kernel of ω. The published unramified characters are the continuous characters H → ℂˣ trivial on H⁰, which is Renard's X(G), and `rationalUnramifiedTwist G ω π` is the published twist π ⊗ ω, acting by ω(g) π(g). So T is Renard's ⋂_{ω ∈ X(G)(π)} ker ω.

Let B be the published full category `RationalInertiaBlock G (rationalInertiaBaseLift G π)`, Renard's M(G)[π], and `CatCenter B` its center. The conclusion asserts a ring isomorphism

e : `MonoidAlgebra ℂ (T ⧸ (rationalCommonNormKernel G).subgroupOf T)` ≃+* `CatCenter B`

such that

1. (scalars) for every c ∈ ℂ and every object X of B, e(`MonoidAlgebra.single 1 c`) acts on X as c • 𝟙;
2. (evaluation) for every t ∈ T, every unramified character ω and every proof hω that the twist `rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π)` lies in B, the image e(`MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)`) of the class of t acts on this twist as ω(t) • 𝟙.

## Correspondence and conventions

**Functions on Irr(G)[π].** The library has no structure of algebraic variety on Irr(G)[π]. The Lean statement uses Renard's own identification of the function algebra with ℂ[T/⁰G] (Remark of VI.4.4), in which the class of t evaluates at the point π ⊗ ω to ω(t). `(rationalCommonNormKernel G).subgroupOf T` is H⁰ ∩ T viewed as a normal subgroup of T; since every unramified character is trivial on H⁰, H⁰ ⊂ T and the quotient is T/⁰G. With (1) and the multiplicativity of e, the element e(f), f = Σ c_t [t], acts on π ⊗ ω by Σ c_t ω(t), which is the value of f at the point π ⊗ ω. So (1) and (2) together say: if z ∈ Z[π] is interpreted as the function e⁻¹(z) on Irr(G)[π], its value at each point π ⊗ ω is the scalar by which z acts on π ⊗ ω. This is the Proposition.

**Every point is reached.** Every irreducible object τ of the block is isomorphic to a twist π ⊗ ω: the published block property says that every irreducible subquotient, in particular τ itself, is related to the lift of π by `IsRationalInertiaRelated`, that is, isomorphic to an actual unramified twist of it. An element of the center acts compatibly with isomorphisms (naturality), so stating (2) on the twists themselves covers every τ ∈ Irr(G)[π]. The membership hω holds for every ω, because an irreducible representation has no irreducible subquotient other than itself up to isomorphism; the statement quantifies over the proof only to avoid proving it inside the statement.

**Why scalars are stated.** e is a ring isomorphism because Mathlib provides no ℂ-algebra structure on `CatCenter B`. Condition (1) says that e is ℂ-linear for the action of ℂ on the block by scalars. Without it a ring isomorphism could twist the coefficients by a field automorphism of ℂ.

**The isomorphism e is Renard's.** Renard's e is the composite ℂ[T/⁰G] ≃ Z ≃ Z[π] of the Proposition of VI.4.4 and the isomorphism of VI.4.5; by the source proof it satisfies (2), and it satisfies (1) because it is ℂ-linear. Conversely (1) and (2) determine e: an element z of Z[π] acting by 0 on every irreducible object of the block is 0. Indeed z_Π then acts by 0 on every simple right R-module, since these are the Hom_G(Π, τ) by the Theorem of VI.4.1 (`RationalSummandHomEquivalenceStatement`) and z_Π acts on Hom_G(Π, τ) as z_τ does; so z_Π = 0 by the Lemma of VI.4.3 (`RationalNormKernelEndSeparationStatement`), and z = 0 because z ↦ z_Π is injective (`RationalSummandBlockCenterStatement`). This argument explains the formulation and is not part of the statement.

**Twists and the universe lift.** The block and the twists are formed from the published `rationalInertiaBaseLift G π`, which applies the fully faithful `SmoothRep.universeLiftFunctor` to π and has carrier in `Type (max uF uV)`, as in the VI.4.1 statements. T is defined from π itself. The published twist uses the same convention as Renard, so ω(t) is not replaced by ω(t)⁻¹.

**The group T.** Renard regards T both as a subgroup of G containing ⁰G and as a sublattice of Λ(G) = G/⁰G. The Lean T is the subgroup of H. The statement does not assert that X(G)(π) is finite or that T has finite index.

**Cuspidality.** Renard's π is supercuspidal. As in the VI.4.1 statements and Worker 1758's `RationalUniversalSmallProgeneratorStatement`, cuspidality is measured by the vanishing of every proper standard normalized Jacquet module. Comparing this with cuspidality along all proper rational parabolics is a separate obligation.

**Universes.** π has carrier in `Type uV` and the block has carriers in `Type (max uF uV)`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

There is no splitness, characteristic-zero, admissibility, compactness or finite-dimensionality premise on π.

## Provenance

The statement is derived from the first Proposition of VI.4.5. The source speaks of the algebra of functions on the variety Irr(G)[π], which is not formalized; the Lean statement replaces it by Renard's identification of this algebra with ℂ[T/⁰G] (Remark of VI.4.4) and states the evaluation property for the basis elements, which is what the source proof establishes. It is made directly for the center of the block, without the intermediate algebras R, A and Z or the choice of ρ, on which the Proposition does not depend.

## Scope

This module defines a Prop-valued target only. It does not prove the statement. The structure of algebraic variety on Irr(G)[π] and its identification with X(G)/X(G)(π) are not formalized. The isomorphism Z[π] ≃ Z(R) is the separate statement `RationalSummandBlockCenterStatement`, the isomorphism ℂ[T/⁰G] ≃ Z(R) is `RationalSummandCenterGroupAlgebraStatement`, and the indecomposability of M(G)[π] is `RationalInertiaBlockIndecomposableStatement`. The bijection SpecMax(Z) → Irr(A), the bijection Irr(A) ≃ Irr(G)[π] and the isomorphism Π/IΠ ≃ m π_I are not stated.
