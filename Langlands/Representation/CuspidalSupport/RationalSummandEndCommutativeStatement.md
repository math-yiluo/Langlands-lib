# Renard VI.4.3, Corollary (ii): End(ind_{⁰G}^G ρ) is commutative exactly when Res π is multiplicity-free

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locators are the opening of VI.4.3, printed p.154 / PDF p.160, and the Lemma, the Corollary and their proofs, including footnote 2, printed p.155 / PDF p.161. The setting is that of VI.4.1–VI.4.2, printed pp.149–153 / PDF pp.155–159. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard keeps the notation of VI.4.1 and VI.4.2: (π,V) is an irreducible supercuspidal representation of G, (ρ,W) is an irreducible summand of the restriction of π to ⁰G, Π = ind_{⁰G}^G ρ, R = End_G(Π), and A = H(G,ρ) is the convolution algebra, isomorphic to R by the Proposition of VI.4.2.

**Corollary (ii).** The algebra A is commutative if and only if the restriction of π to ⁰G is multiplicity-free ("sans multiplicité").

In the proof, m is the multiplicity of ρ in Res π. By the equivalence M(G)[π] ≃ mod-A of VI.4.1, the simple right A-modules are the spaces Hom_{⁰G}(ρ, Res(π⊗ω)) for unramified characters ω of G. Since Res(π⊗ω) = Res π as ⁰G-modules (footnote 2: not as A-modules), each simple right A-module has dimension m. If m = 1, the Lemma of VI.4.3 embeds A in a product of copies of ℂ, so A is commutative. Conversely, if A is commutative, each simple right A-module has dimension 1.

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology.

**`RationalSummandEndCommutativeStatement`.** The premises are exactly those of `RationalSummandSmallProgeneratorStatement`, the Proposition of VI.4.1:

- an arbitrary connected reductive G over an arbitrary nonarchimedean local field F, a maximal split torus inclusion i and a generic cocharacter ν;
- explicit `StandardCocharacterStatement`, relative-root-system and standard-unipotent-closedness premises, from which the finite simple-root index set and the actual semidirect decompositions are derived;
- local compactness, the nonarchimedean group property and Hausdorffness of H;
- π an irreducible actual smooth complex representation of H with carrier in `Type uV`, cuspidal in the sense of the published `Aubert.General.IsCuspidal` (every proper standard normalized Jacquet module vanishes);
- ρ an irreducible actual smooth representation of H⁰ with carrier in `Type uV`, with an injective H⁰-equivariant linear map j : ρ → `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π`.

Let I be the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`. This is Renard's Π, the same object as `rationalNormKernelSummandInduction G ρ` in the VI.4.1 module; it is written out here so that the module does not import that file. `End I` is its endomorphism ring in the category of smooth representations of H. The conclusion is the equivalence of two conditions.

1. `End I` is commutative: α * β = β * α for all α, β ∈ `End I`.
2. For every irreducible actual smooth representation σ of H⁰ with carrier in `Type uV`, the ℂ-vector space of H⁰-equivariant linear maps σ → `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π` has `Module.rank` at most 1.

## Correspondence and conventions

**Multiplicity-free.** Renard's "the restriction of π to ⁰G is multiplicity-free" means that each irreducible representation of ⁰G occurs at most once in Res π. Condition (2) expresses this as dim Hom_{⁰G}(σ, Res π) ≤ 1 for every irreducible σ. By VI.3.2, Res π is a finite direct sum of irreducible representations. For irreducible σ, Schur's lemma then makes dim Hom_{⁰G}(σ, Res π) the number of summands isomorphic to σ. The Lean statement does not use or assert this comparison. Every irreducible σ with a nonzero map to Res π is isomorphic to a subrepresentation of Res π, whose carrier lies in `Type uV`. So quantifying over σ with carrier in `Type uV` loses no isomorphism class that can occur.

Renard's proof uses the multiplicity m of ρ alone. Condition (2) is about all irreducible σ. The two agree because every irreducible summand of Res π is a G-conjugate ρ^g of ρ, and π(g) carries the ρ-isotypic part onto the ρ^g-isotypic part, so all summands occur with the same multiplicity m. The Lean statement does not use or assert this comparison either.

**R versus A.** Renard states the Corollary for A = H(G,ρ). The Lean statement is made for R = `End I`. By the Proposition of VI.4.2, R and A are isomorphic ℂ-algebras, and commutativity is invariant under ring isomorphisms. That Proposition is the separate statement `RationalNormKernelHeckeStatement`. The present statement does not import or use it. Multiplication in `End I` is composition: α * β = β ≫ α, that is α ∘ β.

**Choice of ρ.** As in the VI.4.1 statements, Renard's ρ is an irreducible summand of Res π, and the Lean statement takes every irreducible ρ with an injective equivariant map into Res π. By VI.3.2 these are, up to isomorphism, the summands. The Lean statement does not use or assert this comparison.

**Cuspidality.** Renard's π is supercuspidal. As in the VI.4.1 statements and Worker 1758's `RationalUniversalSmallProgeneratorStatement`, cuspidality is measured by the vanishing of every proper standard normalized Jacquet module. Comparing this with cuspidality along all proper rational parabolics is a separate obligation.

**Universes.** π, ρ and σ have carriers in `Type uV`, and I has carrier in `Type (max uF uV)`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

There is no splitness, characteristic-zero, admissibility, compactness or finite-dimensionality premise on ρ or π.

## Provenance

Unlike the Lemma and Corollary (i), part (ii) is kept in Renard's setting: an irreducible cuspidal π and an irreducible ρ embedded in Res π. Its proof uses the equivalence of categories of VI.4.1, which needs that setting, and condition (2) refers to π. The provenance is recorded as source.

## Scope

This module defines a Prop-valued target only. It does not prove the statement. The Lemma of VI.4.3 is the separate statement `RationalNormKernelEndSeparationStatement`, and part (i) of the Corollary is the separate statement `RationalNormKernelEndDomainStatement`. The equivalence of categories of VI.4.1 is the separate statement `RationalSummandHomEquivalenceStatement`. The later results of VI.4 (the center of R and of the block) are not stated here.
