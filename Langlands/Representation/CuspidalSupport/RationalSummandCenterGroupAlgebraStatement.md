# Renard VI.4.4, Proposition: the center of End(ind_{⁰G}^G ρ) is ℂ[T/⁰G]

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locators are the Proposition of VI.4.4 and its proof, printed p.159 / PDF p.165. The Proposition refers back to the definition of T and the Remark, printed pp.156–157 / PDF pp.162–163, to the Lemma of VI.4.4 (ρ_T), printed pp.157–158 / PDF pp.163–164, and to the proof of the Theorem of VI.4.4, including (VI.4.4.5)–(VI.4.4.7), printed pp.158–159 / PDF pp.164–165. The scalar by which ψ_x acts is also used in the proof of the first Proposition of VI.4.5, printed p.160 / PDF p.166. The setting is that of VI.4.1–VI.4.3, printed pp.149–155 / PDF pp.155–161. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard keeps the notation of VI.4.1–VI.4.4: (π,V) is an irreducible supercuspidal representation of G, (ρ,W) is an irreducible summand of the restriction of π to ⁰G, Π = ind_{⁰G}^G ρ, R = End_G(Π), A = H(N,ρ) is the convolution algebra of VI.4.2–VI.4.3, isomorphic to R, and Z = H(T,ρ) is its center (Theorem of VI.4.4). Here X(G) is the torus of unramified characters, X(G)(π) = {ω | π ⊗ ω ≃ π}, and T = ⋂_{ω ∈ X(G)(π)} ker ω. In the preliminary remarks of VI.4.4 Renard replaces W by another copy of ρ in V so that H = {g | π(g) W = W} has the properties used later. ρ_H is the resulting representation of H on W, and ρ_T is its restriction to T ⊂ H (Lemma of VI.4.4).

**Proposition.** For every g ∈ T, let ψ_g be the element of Z with support ⁰G g⁻¹, normalized as in the proof of the Theorem, that is ψ_g(g⁻¹) = ρ_T(g⁻¹). Then g ↦ ψ_g induces an isomorphism ℂ[T/⁰G] ≃ Z. This shows that Z is isomorphic to the algebra of functions on the variety Irr(G)[π].

The proof says that the isomorphism follows easily from (VI.4.3.2), and that the algebra of functions on Irr(G)[π] is ℂ[T/⁰G] by the Remark of VI.4.4.

In the proof of the Theorem, (VI.4.4.7) shows that an element φ of A supported on ⁰G g, with g ∈ T and φ(g) = ρ_T(g), acts on the simple right A-module Hom_{⁰G}(ρ, π ⊗ ω) by multiplication by ω(g⁻¹), for every ω ∈ X(G). Applied to ψ_g (support ⁰G g⁻¹, ψ_g(g⁻¹) = ρ_T(g⁻¹)) this gives the scalar ω(g). The proof of the first Proposition of VI.4.5 uses exactly this: ψ_x acts on Hom_{⁰G}(ρ, π ⊗ ω) by ω(x).

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology. (In this file H denotes G(F), not Renard's stabilizer of W.)

**`RationalSummandCenterGroupAlgebraStatement`.** The premises are exactly those of `RationalSummandSmallProgeneratorStatement`, the Proposition of VI.4.1, with the maximal split torus renamed S:

- an arbitrary connected reductive G over an arbitrary nonarchimedean local field F, a maximal split torus inclusion i : S → G and a generic cocharacter ν;
- explicit `StandardCocharacterStatement`, relative-root-system and standard-unipotent-closedness premises, from which the finite simple-root index set and the actual semidirect decompositions are derived;
- local compactness, the nonarchimedean group property and Hausdorffness of H;
- π an irreducible actual smooth complex representation of H with carrier in `Type uV`, cuspidal in the sense of the published `Aubert.General.IsCuspidal` (every proper standard normalized Jacquet module vanishes);
- ρ an irreducible actual smooth representation of H⁰ with carrier in `Type uV`, with an injective H⁰-equivariant linear map j : ρ → `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π`.

The statement then introduces three local abbreviations, exactly as in `RationalSummandEndCenterStatement`.

- T is the subgroup of H given by the infimum, over all ω in the published `unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)` with `Nonempty (rationalUnramifiedTwist G ω π ≅ π)`, of the kernel of ω. The published unramified characters are the continuous characters H → ℂˣ trivial on H⁰, which is Renard's X(G), and `rationalUnramifiedTwist G ω π` is the published twist π ⊗ ω, acting by ω(g) π(g). So T is Renard's ⋂_{ω ∈ X(G)(π)} ker ω.
- I is the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`. This is Renard's Π: functions f : H → W with f(hx) = ρ(h) f(x) for h ∈ H⁰, compactly supported modulo H⁰, with H acting by right translation. `End I` is its endomorphism ring in the category of smooth representations of H.
- For w ∈ W, f(w) is the published `Induction.unitFunction` of the open adjunction. By the published `eval_unitFunction`, f(w)(x) = ρ(x) w for x ∈ H⁰ and f(w)(x) = 0 otherwise, so f(w) is Renard's f_w of (VI.4.1.2).

The conclusion asserts the existence of a ℂ-algebra isomorphism

e : `MonoidAlgebra ℂ (T ⧸ (rationalCommonNormKernel G).subgroupOf T)` ≃ₐ[ℂ] `Subalgebra.center ℂ (End I)`

such that for every t ∈ T, writing ψ = e(`MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)`) for the image of the basis element of the class of t:

1. (support) for every w ∈ W and every g ∈ H with g t ∉ H⁰, the value at g of ψ(f(w)) (the published `Induction.eval`) is 0;
2. (action) for every unramified character ω and every morphism φ : I → `rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π)` of smooth representations of H, ψ ≫ φ = ω(t) • φ.

## Correspondence and conventions

**The group algebra.** `(rationalCommonNormKernel G).subgroupOf T` is H⁰ ∩ T viewed as a subgroup of T. It is normal (the published instance `rationalCommonNormKernel_normal`), so the quotient is a group, and `MonoidAlgebra ℂ` of it is the group algebra ℂ[T/H⁰] with basis `MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)`, t ∈ T. Every unramified character is trivial on H⁰, so H⁰ ⊂ T and the quotient is Renard's T/⁰G. "g ↦ ψ_g induces an isomorphism ℂ[T/⁰G] ≃ Z" means that the linear map sending the basis element of t⁰G to ψ_t is an algebra isomorphism; the Lean statement asserts an algebra isomorphism e and identifies the image of each basis element by (1) and (2).

**R versus A, center and support.** Renard states the Proposition for A = H(N,ρ) and its center Z. The Lean statement is made for R = `End I` and its center `Subalgebra.center ℂ (End I)`. The Proposition of VI.4.2, stated separately as `RationalNormKernelHeckeStatement`, identifies R with A by α ↦ φ_α, φ_α(g)(w) = α(f_w)(g). Condition (1) says that φ_ψ vanishes outside H⁰t⁻¹, that is, ψ has Renard's support ⁰G t⁻¹. Since e is injective, ψ ≠ 0, so its support is exactly this coset. The present statement does not import or use the VI.4.2 statement.

**The normalization of ψ_g.** Renard normalizes ψ_g by ψ_g(g⁻¹) = ρ_T(g⁻¹). This uses ρ_T, which depends on the choice of W made in the preliminary remarks of VI.4.4 and on the Lemma of VI.4.4, neither of which is formalized. The Lean statement replaces the normalization by the action condition (2). Renard's ψ_g satisfies (2): this is (VI.4.4.7), transported along the Frobenius reciprocity Hom_G(Π, σ) ≃ Hom_{⁰G}(ρ, σ), Φ ↦ (w ↦ Φ(f_w)). Explicitly, if α ∈ R has α(f_w) supported on H⁰s with α(f_w)(s) = A w, then α(f_w) = s⁻¹ · f_{Aw}, hence (α ≫ Φ)(f_w) = σ(s⁻¹) Φ(f_{Aw}); for α = ψ_t one has s = t⁻¹ and A = ρ_T(t⁻¹), and the computation of (VI.4.4.7) gives ω(t) Φ(f_w) for σ = π ⊗ ω. Conversely, (2) determines ψ: the simple right R-modules are, through the equivalence of VI.4.1 (`RationalSummandHomEquivalenceStatement`), the spaces Hom_G(Π, τ) for τ irreducible in M(G)[π], and by the definition of the block these τ are the unramified twists π ⊗ ω; an element acting by zero on all of them is 0 by the Lemma of VI.4.3 (`RationalNormKernelEndSeparationStatement`). So the e of the Lean statement is Renard's isomorphism. This argument explains the formulation and is not part of the statement. In R, a morphism Φ : Π → σ is acted on by α through precomposition, Φ ↦ α ≫ Φ; this is the right R-module structure of VI.4.1. Multiplication in `End I` is α * β = β ≫ α; for central ψ the order does not matter.

**The universe lift.** I has carrier in `Type (max uF uV)` and π in `Type uV`. Morphisms I → π ⊗ ω therefore go to the published `rationalInertiaBaseLift G π`, which applies the published fully faithful `SmoothRep.universeLiftFunctor` (carrier `ULift π`), as in the VI.4.1 statements; the twist is applied to the lifted representation.

**The group T.** Renard regards T both as a subgroup of G containing ⁰G and as a sublattice of Λ(G) = G/⁰G. The Lean T is the subgroup of H. The statement does not assert that X(G)(π) is finite or that T has finite index.

**Choice of ρ.** As in the VI.4.1 statements, Renard's ρ is an irreducible summand of Res π, and the Lean statement takes every irreducible ρ with an injective equivariant map into Res π. By VI.3.2 these are, up to isomorphism, the summands. The replacement of W in Renard's preliminary remarks changes neither ρ up to isomorphism nor R, and the Lean statement does not depend on it.

**Cuspidality.** Renard's π is supercuspidal. As in the VI.4.1 statements and Worker 1758's `RationalUniversalSmallProgeneratorStatement`, cuspidality is measured by the vanishing of every proper standard normalized Jacquet module. Comparing this with cuspidality along all proper rational parabolics is a separate obligation.

**Universes.** π and ρ have carriers in `Type uV`, and I has carrier in `Type (max uF uV)`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

There is no splitness, characteristic-zero, admissibility, compactness or finite-dimensionality premise on ρ or π.

## Provenance

The statement is derived from the Proposition of VI.4.4. It keeps Renard's setting (an irreducible cuspidal π and an irreducible ρ embedded in Res π), on which T and Π depend. It is stated for R instead of A, and it replaces Renard's W-dependent normalization ψ_g(g⁻¹) = ρ_T(g⁻¹) by the action of ψ_g on Hom_G(Π, π ⊗ ω) by ω(g), which Renard derives in (VI.4.4.7) and uses in VI.4.5. As explained above, this condition determines ψ_g.

## Scope

This module defines a Prop-valued target only. It does not prove the statement. The final sentence of the Proposition, that Z is isomorphic to the algebra of functions on the variety Irr(G)[π], is not stated; the library has no algebraic-variety structure on Irr(G)[π]. The Lemma of VI.4.4 and ρ_T are not stated. The Theorem of VI.4.4 is the separate module `RationalSummandEndCenterStatement`, and the Corollary of VI.4.4 is the separate module `RationalSummandEndNoetherianStatement`.
