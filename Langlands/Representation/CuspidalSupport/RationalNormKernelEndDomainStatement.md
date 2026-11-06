# Renard VI.4.3, Corollary (i): End(ind_{⁰G}^G ρ) is a domain

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locators are the opening of VI.4.3 with the relations (VI.4.3.1)–(VI.4.3.3), printed p.154 / PDF p.160, and the Lemma, the Corollary and their proofs, printed p.155 / PDF p.161. The algebra R and its identification with H(G,ρ) are from VI.4.1–VI.4.2, printed pp.149–153 / PDF pp.155–159. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard keeps the notation of VI.4.1 and VI.4.2: (π,V) is an irreducible supercuspidal representation of G, (ρ,W) is an irreducible summand of the restriction of π to ⁰G, Π = ind_{⁰G}^G ρ, R = End_G(Π), and A = H(G,ρ) is the convolution algebra, isomorphic to R by the Proposition of VI.4.2. In VI.4.3 he shows that A is a "twisted" Laurent polynomial algebra over the lattice ⁰G\N, where N is the stabilizer of ρ in G. The Lemma of VI.4.3 says that A is separated by its simple right modules.

**Corollary (i).** The algebra A is a domain ("intègre"), so it has no nonzero nilpotent element.

Renard says that (i) follows immediately from the Lemma.

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology.

**`RationalNormKernelEndDomainStatement`.** Take an arbitrary nonarchimedean local field F in universe uF and an actual connected reductive group scheme G over Spec F. Let ρ be an irreducible smooth complex representation of H⁰ with carrier in `Type uV` (`SmoothRep.IsIrreducible`). Let I be the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`. This is ind_{H⁰}^H ρ, an actual smooth representation of H with carrier in `Type (max uF uV)`. `End I` is its endomorphism ring in the category of smooth representations of H, whose morphisms are the H-equivariant linear maps. The statement asserts `IsDomain (End I)`.

## Correspondence and conventions

**Domain.** Mathlib's `IsDomain` for a possibly noncommutative ring means that the ring is nontrivial (1 ≠ 0) and that multiplication by a nonzero element is cancellative on both sides. For rings this is the same as having no zero divisors. This is Renard's "intègre" for a noncommutative algebra. Renard's consequence, that A has no nonzero nilpotent element, follows from `IsDomain` and is not stated separately. Multiplication in `End I` is composition: α * β = β ≫ α, that is α ∘ β.

**R versus A.** Renard states the Corollary for A = H(G,ρ). The Lean statement is made for R = `End I`. By the Proposition of VI.4.2, R and A are isomorphic ℂ-algebras, and being a domain is invariant under ring isomorphisms. That Proposition is the separate statement `RationalNormKernelHeckeStatement`. The present statement does not import or use it.

**Universes.** ρ has carrier in `Type uV` and I has carrier in `Type (max uF uV)`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

## Generalization and provenance

Renard proves the Corollary for one irreducible summand ρ of the restriction to ⁰G of an irreducible supercuspidal π. The Lean statement is made for every irreducible smooth representation ρ of H⁰, for every connected reductive G over a nonarchimedean local field. It has no maximal split torus, cocharacter, root system or topological premise and no representation π. So the statement is derived from the source rather than a literal transcription. Its provenance is recorded as derived. Renard's ρ is in particular an irreducible smooth representation of H⁰, so his Corollary (i) is a special case.

The reason for the generalization is that the structure of A in VI.4.3 does not use π. The passage from R to A is the Proposition of VI.4.2, whose proof uses only that ⁰G is open and normal in G (see the Markdown of `RationalNormKernelHeckeStatement`, which is stated for every irreducible ρ). For A, Renard's computation uses the following facts.

- dim F_x(ρ) ≤ 1, with equality exactly for x in the stabilizer N, by Schur's lemma for ρ. Irreducible smooth representations of ⁰G have countable dimension, since ⁰G has only countably many cosets of each open subgroup.
- The product of nonzero elements of F_x(ρ) and F_y(ρ) is a nonzero element of F_{xy}(ρ) (VI.4.3.1).
- ⁰G\N is a free abelian group of finite rank. It is a subgroup of Λ(G) = ⁰G\G, which is free abelian of finite rank (V.2.6).

So A is graded by the free abelian group ⁰G\N, with one-dimensional pieces whose nonzero elements multiply to nonzero elements. Such an algebra is a domain: after fixing a total order on ⁰G\N compatible with the group law, the product of two nonzero elements has a nonzero leading term. None of these facts uses π or supercuspidality. The separation statement of the Lemma likewise holds for every irreducible ρ (see `RationalNormKernelEndSeparationStatement`).

## Scope

This module defines a Prop-valued target only. It does not prove the statement. The Lemma of VI.4.3 is the separate statement `RationalNormKernelEndSeparationStatement`, and part (ii) of the Corollary is the separate statement `RationalSummandEndCommutativeStatement`.
