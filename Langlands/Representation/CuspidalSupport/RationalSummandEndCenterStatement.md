# Renard VI.4.4, Theorem: the center of End(ind_{⁰G}^G ρ) and the rank over it

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locators are the preliminary remarks of VI.4.4, including (VI.4.4.1), (VI.4.4.2), the definition of T and the Remark, printed pp.155–157 / PDF pp.161–163; the Lemma of VI.4.4 and its proof, printed pp.157–158 / PDF pp.163–164; and the Theorem and its proof, including (VI.4.4.5)–(VI.4.4.7), printed pp.158–159 / PDF pp.164–165. The setting is that of VI.4.1–VI.4.3, printed pp.149–155 / PDF pp.155–161. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard keeps the notation of VI.4.1–VI.4.3: (π,V) is an irreducible supercuspidal representation of G, (ρ,W) is an irreducible summand of the restriction of π to ⁰G, Π = ind_{⁰G}^G ρ, R = End_G(Π), and A = H(G,ρ) is the convolution algebra of VI.4.2, isomorphic to R. N is the stabilizer of ρ in G. At the opening of VI.4.3 (printed p.154 / PDF p.160), the elements of A supported in ⁰G x correspond to the intertwining operators ρ^x → ρ, so they are zero unless x ∈ N, and Renard writes A = H(N,ρ). For a subgroup L of G containing ⁰G, H(L,ρ) denotes the elements of A supported in L.

X(G) is the complex torus of unramified characters of G, and X(G)(π) = {ω ∈ X(G) | π ⊗ ω ≃ π} is its finite subgroup (V.2.7). Renard defines

T = ⋂_{ω ∈ X(G)(π)} ker ω,

a subgroup of G containing ⁰G Z(G), hence of finite index. Let m be the multiplicity of ρ in Res^G_{⁰G} π.

**Theorem.** The center of A = H(N,ρ) is Z = H(T,ρ). In particular, A is a free Z-module of rank m².

In the proof, an element of Z supported on one coset ⁰G g acts on each simple right A-module Hom_{⁰G}(ρ, π ⊗ ω) by a scalar; by (VI.4.4.5) this forces g ∈ H and then ω(g) = 1 for every ω ∈ X(G)(π), so g ∈ T. Conversely, by (VI.4.4.7), an element supported on ⁰G g with g ∈ T acts on every simple right A-module by the scalar ω(g⁻¹), and the Lemma of VI.4.3 then shows that it is central. Finally [N : T] = m² by the Lemma of VI.4.4, and nonzero elements φ_i of A supported on the cosets ⁰G n_i, for representatives n_1, …, n_{m²} of T in N, form a basis of A over Z.

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology.

**`RationalSummandEndCenterStatement`.** The premises are exactly those of `RationalSummandSmallProgeneratorStatement`, the Proposition of VI.4.1, with the maximal split torus renamed S:

- an arbitrary connected reductive G over an arbitrary nonarchimedean local field F, a maximal split torus inclusion i : S → G and a generic cocharacter ν;
- explicit `StandardCocharacterStatement`, relative-root-system and standard-unipotent-closedness premises, from which the finite simple-root index set and the actual semidirect decompositions are derived;
- local compactness, the nonarchimedean group property and Hausdorffness of H;
- π an irreducible actual smooth complex representation of H with carrier in `Type uV`, cuspidal in the sense of the published `Aubert.General.IsCuspidal` (every proper standard normalized Jacquet module vanishes);
- ρ an irreducible actual smooth representation of H⁰ with carrier in `Type uV`, with an injective H⁰-equivariant linear map j : ρ → `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π`.

The statement then introduces three local abbreviations.

- T is the subgroup of H given by the infimum, over all ω in the published `unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)` with `Nonempty (rationalUnramifiedTwist G ω π ≅ π)`, of the kernel of ω. The published unramified characters are the continuous characters H → ℂˣ trivial on H⁰, which is Renard's X(G), and `rationalUnramifiedTwist G ω π` is the published twist π ⊗ ω, acting by ω(g) π(g). So T is Renard's ⋂_{ω ∈ X(G)(π)} ker ω.
- I is the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`. This is Renard's Π, the same object as `rationalNormKernelSummandInduction G ρ` in the VI.4.1 module; it is written out so that the module does not import that file. `End I` is its endomorphism ring in the category of smooth representations of H.
- For w ∈ W, f(w) is the published `Induction.unitFunction` of the open adjunction. By the published `eval_unitFunction`, f(w)(x) = ρ(x) w for x ∈ H⁰ and f(w)(x) = 0 otherwise, so f(w) is Renard's f_w of (VI.4.1.2).

The conclusion is the conjunction of two assertions.

1. For every α ∈ `End I`, α lies in `Subalgebra.center ℂ (End I)` if and only if, for every w ∈ W and every g ∈ H with g ∉ T, the value at g of α(f(w)) (the published `Induction.eval`) is 0.
2. There is a natural number m such that the `Module.rank` over ℂ of the space of H⁰-equivariant maps ρ → `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π` equals m, and `End I` has a basis indexed by `Fin (m ^ 2)` as a module over `Subalgebra.center ℂ (End I)`.

## Correspondence and conventions

**R versus A, and the support condition.** Renard states the Theorem for A = H(N,ρ). The Lean statement is made for R = `End I`. The Proposition of VI.4.2, stated separately as `RationalNormKernelHeckeStatement`, identifies R with A by α ↦ φ_α, φ_α(g)(w) = α(f_w)(g). So assertion (1) says that α is central exactly when φ_α vanishes outside T, that is, φ_α ∈ H(T,ρ). This is Renard's Z = H(T,ρ) transported to R. The present statement does not import or use the VI.4.2 statement; it expresses the support condition directly through the values α(f_w)(g).

**Center and module structure.** `Subalgebra.center ℂ (End I)` is Mathlib's center of the ℂ-algebra `End I`: the elements commuting with every element. Multiplication in `End I` is composition: α * β = β ≫ α. The module structure of `End I` over the center is Mathlib's `Subalgebra.moduleLeft`, multiplication on the left by central elements; since these elements are central this agrees with multiplication on the right. Assertion (2) is Renard's "A is a free Z-module of rank m²", with the basis indexed by `Fin (m ^ 2)`.

**The multiplicity m.** Renard's m is the multiplicity of ρ in Res π. By VI.3.2, Res π is a finite direct sum of irreducible representations of ⁰G, and Schur's lemma for ρ makes dim Hom_{⁰G}(ρ, Res π) the number of summands isomorphic to ρ. Assertion (2) takes m to be this dimension, `Module.rank ℂ (ρ ⟶ Res π)`, and asserts that it is finite. The Lean statement does not use or assert the comparison with the decomposition of VI.3.2.

**The group T.** Renard regards T both as a subgroup of G containing ⁰G and as a sublattice of Λ(G) = G/⁰G. The Lean T is the subgroup of H. The statement does not assert that X(G)(π) is finite or that T has finite index; these facts are used in Renard's proof but are not part of the Theorem. The library's `Plancherel.unramifiedTwistStabilizer` is defined for admissible irreducible classes; the Lean statement does not use it and writes the twist condition directly as the existence of an isomorphism π ⊗ ω ≅ π of smooth representations.

**Choice of ρ.** As in the VI.4.1 statements, Renard's ρ is an irreducible summand of Res π, and the Lean statement takes every irreducible ρ with an injective equivariant map into Res π. By VI.3.2 these are, up to isomorphism, the summands. Renard's proof replaces the subspace W by another copy of ρ in V so that H = {g | π(g) W = W} equals the normalizer of ρ_H. This choice changes neither ρ up to isomorphism nor A, so the Theorem, which is about A, does not depend on it. The Lean statement involves neither H nor this choice.

**Cuspidality.** Renard's π is supercuspidal. As in the VI.4.1 statements and Worker 1758's `RationalUniversalSmallProgeneratorStatement`, cuspidality is measured by the vanishing of every proper standard normalized Jacquet module. Comparing this with cuspidality along all proper rational parabolics is a separate obligation.

**Universes.** π and ρ have carriers in `Type uV`, and I has carrier in `Type (max uF uV)`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

There is no splitness, characteristic-zero, admissibility, compactness or finite-dimensionality premise on ρ or π.

## Provenance

The statement is kept in Renard's setting: an irreducible cuspidal π and an irreducible ρ embedded in Res π. Both T and m are defined through π, and Renard's proof uses the equivalence of categories of VI.4.1 and the Lemma of VI.4.4, which need that setting. The provenance is recorded as source.

## Scope

This module defines a Prop-valued target only. It does not prove the statement. It does not state the Lemma of VI.4.4 (T ⊂ H ⊂ N with [N : H] = [H : T] = m, and the restriction isomorphism (VI.4.4.3)), which depends on the choice of W. The Corollary of VI.4.4 (A is noetherian) and the Proposition of VI.4.4 (Z ≃ ℂ[T/⁰G]) are not stated here. The VI.4.1–VI.4.3 statements are the separate modules `RationalSummandSmallProgeneratorStatement`, `RationalSummandHomEquivalenceStatement`, `RationalNormKernelHeckeStatement`, `RationalNormKernelEndSeparationStatement`, `RationalNormKernelEndDomainStatement` and `RationalSummandEndCommutativeStatement`.
