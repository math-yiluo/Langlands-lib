# Renard VI.4.3, Lemma: simple right modules separate End(ind_{⁰G}^G ρ)

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locators are the opening of VI.4.3, the spaces F_x(ρ), the relations (VI.4.3.1)–(VI.4.3.3) and the statement of the Lemma, printed p.154 / PDF p.160, and the end of the Lemma with its proof, printed p.155 / PDF p.161. The algebra R and its identification with H(G,ρ) are from VI.4.1–VI.4.2, printed pp.149–153 / PDF pp.155–159. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard keeps the notation of VI.4.1 and VI.4.2: (π,V) is an irreducible supercuspidal representation of G, (ρ,W) is an irreducible summand of the restriction of π to ⁰G, Π = ind_{⁰G}^G ρ, R = End_G(Π), and A = H(G,ρ) is the convolution algebra, isomorphic to R by the Proposition of VI.4.2.

For x ∈ G, F_x(ρ) is the space of φ ∈ A with support in ⁰G x. Evaluation at x identifies F_x(ρ) with Hom_{⁰G}(ρ^x, ρ), so dim F_x(ρ) ≤ 1, with equality exactly when x lies in the stabilizer N of ρ. By (VI.4.3.1), the product of nonzero elements of F_x(ρ) and F_y(ρ) is a nonzero element of F_{xy}(ρ). So every nonzero element of F_x(ρ) is invertible, and A is a "twisted" Laurent polynomial algebra over the lattice ⁰G\N. By (VI.4.3.3), its units are the monomials c φ₁^{e₁} ∗ ⋯ ∗ φₙ^{eₙ} with c ∈ ℂ^×.

**Lemma.** For every right A-module M, let A → End_ℂ(M), φ ↦ φ_M, be the map giving the module structure. Fix a system of representatives of the isomorphism classes of simple right A-modules. Then the map A → ∏ End_ℂ(M), φ ↦ (φ_M), with the product over that system, is injective.

The proof uses the separation lemma of B.III: an element φ of the kernel is nilpotent. Then 1 + φ and 1 − φ² are units, and the form (VI.4.3.3) of the units forces 1 + φ to be a scalar, so φ = 0.

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology.

**`RationalNormKernelEndSeparationStatement`.** Take an arbitrary nonarchimedean local field F in universe uF and an actual connected reductive group scheme G over Spec F. Let ρ be an irreducible smooth complex representation of H⁰ with carrier in `Type uV` (`SmoothRep.IsIrreducible`). Let I be the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`. This is ind_{H⁰}^H ρ, an actual smooth representation of H with carrier in `Type (max uF uV)`. `End I` is its endomorphism ring in the category of smooth representations of H, whose morphisms are the H-equivariant linear maps.

The statement asserts: for every α ∈ `End I`, if `MulOpposite.op α • m = 0` for every type M in `Type (max uF uV)`, every module structure of M over `(End I)ᵐᵒᵖ` with `IsSimpleModule (End I)ᵐᵒᵖ M`, and every m ∈ M, then α = 0.

## Correspondence and conventions

**Right modules.** In Mathlib, multiplication in `End I` is composition: α * β = β ≫ α, that is α ∘ β. A right R-module is a module over the opposite ring Rᵐᵒᵖ, with m · α written `MulOpposite.op α • m`. So the hypothesis says that α acts as zero on every simple right R-module, that is α_M = 0 for every such M. The conclusion α = 0 is the injectivity of φ ↦ (φ_M). Mathlib modules are unital, as are Renard's modules in M(A)_d.

**Representatives of simple modules.** Renard takes the product over a system of representatives of the isomorphism classes. The Lean statement quantifies over all simple modules with carrier in `Type (max uF uV)`. These give the same kernel. Every simple right R-module is cyclic, so it is isomorphic to a quotient of R by a maximal right ideal. That quotient has carrier in `Type (max uF uV)`, the universe of `End I`. So every isomorphism class has a member in this universe.

**R versus A.** Renard states the Lemma for A = H(G,ρ). The Lean statement is made for R = `End I`. By the Proposition of VI.4.2, R and A are isomorphic ℂ-algebras, and the property in the Lemma is invariant under ring isomorphisms. That Proposition is the separate statement `RationalNormKernelHeckeStatement`. The present statement does not import or use it.

**Universes.** ρ has carrier in `Type uV` and I has carrier in `Type (max uF uV)`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

## Generalization and provenance

Renard proves the Lemma for one irreducible summand ρ of the restriction to ⁰G of an irreducible supercuspidal π. The Lean statement is made for every irreducible smooth representation ρ of H⁰, for every connected reductive G over a nonarchimedean local field. It has no maximal split torus, cocharacter, root system or topological premise and no representation π. So the statement is derived from the source rather than a literal transcription. Its provenance is recorded as derived. Renard's ρ is in particular an irreducible smooth representation of H⁰, so his Lemma is a special case.

The passage from R to A is the Proposition of VI.4.2, whose proof uses only that ⁰G is open and normal in G (see the Markdown of `RationalNormKernelHeckeStatement`, which is stated for every irreducible ρ). Renard's argument for A uses the following facts.

- dim F_x(ρ) ≤ 1, by Schur's lemma for ρ. Irreducible smooth representations of ⁰G have countable dimension, since ⁰G has only countably many cosets of each open subgroup.
- ⁰G\N is a free abelian group of finite rank. It is a subgroup of Λ(G) = ⁰G\G, which is free abelian of finite rank (V.2.6). Renard also notes that ⁰G\N has the same rank as Λ(G), because N contains ⁰G Z(G). The Lemma does not need this.
- A has countable dimension, so the separation lemma of B.III applies.

None of these facts uses π or supercuspidality.

## Scope

This module defines a Prop-valued target only. It does not prove the statement. It does not state the description of F_x(ρ), the twisted Laurent polynomial structure of A or the description (VI.4.3.3) of its units. Those are steps of Renard's argument, not statements of the Lemma. The Corollary of VI.4.3 is stated in two separate modules: `RationalNormKernelEndDomainStatement` (part (i)) and `RationalSummandEndCommutativeStatement` (part (ii)).
