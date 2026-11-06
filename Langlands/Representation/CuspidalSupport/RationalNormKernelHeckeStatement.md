# Renard VI.4.2: the convolution algebra H(G,ρ) and the endomorphisms of ind_{⁰G}^G ρ

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locators are the definition of f_w in (VI.4.1.2), printed p.149 / PDF p.155; the definition (VI.4.2.1) of H(G,ρ), its convolution product and unit, printed p.151 / PDF p.157; and the Proposition of VI.4.2 with its proof, including (VI.4.2.2)–(VI.4.2.4), printed p.152 / PDF p.158. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard keeps the notation of VI.4.1: (π,V) is an irreducible supercuspidal representation of G, (ρ,W) is an irreducible summand of the restriction of π to ⁰G, (Π,V_Π) = ind_{⁰G}^G(ρ,W) and R = End_G(Π). He defines H(G,ρ) as the set of functions φ : G → End_ℂ(W) such that

1. φ(h g h') = ρ(h) φ(g) ρ(h') for g ∈ G and h, h' ∈ ⁰G (VI.4.2.1);
2. Supp(φ) is a finite union of left cosets modulo ⁰G.

The convolution product is (φ ∗ ψ)(x) = ∑_{ḡ ∈ G/⁰G} φ(g) ψ(g⁻¹x), summed over a system of representatives; the result does not depend on that choice. The unit φ_e satisfies φ_e(1) = Id_W and φ_e(g) = 0 for g ∉ ⁰G. For w ∈ W, f_w ∈ V_Π is the function with f_w(1) = w and Supp f_w ⊂ ⁰G (VI.4.1.2).

**Proposition.** The maps R → H(G,ρ), α ↦ φ_α with φ_α(g)(w) = α(f_w)(g), and H(G,ρ) → R, φ ↦ α_φ with α_φ(f)(x) = ∑_{ḡ ∈ ⁰G\G} φ(g)(f(g⁻¹x)), are mutually inverse isomorphisms of ℂ-algebras.

The proof uses the decomposition f = ∑_{ḡ ∈ ⁰G\G} r(g⁻¹)·f_{f(g)} of every f ∈ V_Π (VI.4.2.2), a finite sum, and compares (VI.4.2.3) with (VI.4.2.4) by a change of variable.

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology. The published `isOpen_rationalCommonNormKernel` says that H⁰ is open, and the published instance `rationalCommonNormKernel_normal` says that it is normal.

**`rationalNormKernelHecke G ρ`.** For a smooth complex representation ρ of H⁰, this is the ℂ-submodule of all functions φ : H → `Module.End ℂ ρ` such that

1. φ(h g h') = ρ(h) φ(g) ρ(h') for all h, h' ∈ H⁰ and g ∈ H (`*` in `Module.End` is composition);
2. the image of the support of φ in H ⧸ H⁰ (Mathlib's `QuotientGroup.mk`, cosets g H⁰) is a finite set.

The submodule proof checks closure under zero, addition and scalar multiplication. This is Renard's H(G,ρ) as a vector space.

**`rationalNormKernelConvolution G ρ φ ψ`.** For arbitrary functions φ, ψ : H → `Module.End ℂ ρ`, this is the function

x ↦ ∑ᶠ_{q ∈ H ⧸ H⁰} φ(q.out) ∘ ψ(q.out⁻¹ x),

where `q.out` is the representative of the coset q chosen by `Quotient.out`. This is Renard's convolution with one fixed system of representatives. The definition does not assert that the value is independent of the representatives, and it does not put a ring structure on H(G,ρ).

**`RationalNormKernelHeckeStatement`.** Take an arbitrary nonarchimedean local field F in universe uF and an actual connected reductive group scheme G over Spec F, with H⁰ as above. Let ρ be an irreducible smooth complex representation of H⁰ with carrier in `Type uV` (`SmoothRep.IsIrreducible`, that is Mathlib's `Representation.IsIrreducible`). Let I be the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`. This is ind_{H⁰}^H ρ: functions f : H → W with f(h x) = ρ(h) f(x), fixed by an open subgroup under right translation, and with support compact modulo H⁰. H acts by right translation. For w ∈ W, let f_w be the published `Induction.unitFunction` of the open adjunction. By the published `eval_unitFunction`, f_w(x) = ρ(x) w for x ∈ H⁰ and f_w(x) = 0 otherwise, so f_w is Renard's f_w. The statement asserts that there is a ℂ-linear equivalence e : `End I ≃ₗ[ℂ] rationalNormKernelHecke G ρ` with the following three properties.

1. For every α ∈ End I, g ∈ H and w ∈ W, e(α)(g)(w) = α(f_w)(g). So e is Renard's α ↦ φ_α.
2. For every φ in H(G,ρ), v ∈ I and x ∈ H, e⁻¹(φ)(v)(x) = ∑ᶠ_{q ∈ H⁰\H} φ(q.out)(v(q.out⁻¹ x)). Here H⁰\H is the published `LeftQuotient (rationalCommonNormKernel G)`, the quotient by the cosets H⁰ g. So e⁻¹ is Renard's φ ↦ α_φ.
3. For all α, β ∈ End I, e(α * β) = `rationalNormKernelConvolution G ρ (e α) (e β)`.

## Correspondence and conventions

**Multiplication in End I.** In Mathlib, α * β in `End I` is composition: α * β = β ≫ α, that is α ∘ β. So (3) is Renard's identity φ_{αβ} = φ_α ∗ φ_β, with (VI.4.2.3) on the left and (VI.4.2.4) on the right. The linear structure on `End I` is Mathlib's ℂ-linear structure on the full subcategory of smooth representations inside `Rep ℂ H⁰`.

**Algebra isomorphism.** Renard states an isomorphism of ℂ-algebras. The Lean statement does not define an algebra structure on H(G,ρ). It asserts a linear bijection e that carries composition to the convolution of `rationalNormKernelConvolution`. Since e is bijective, (3) transports the algebra structure of End I: convolution preserves H(G,ρ), it is associative on H(G,ρ), and e(1) is a two-sided unit. By (1) and `eval_unitFunction`, e(1)(g) is ρ(g) for g ∈ H⁰ and 0 otherwise, which is Renard's φ_e. Properties (1) and (2) identify e and e⁻¹ with Renard's two maps α ↦ φ_α and φ ↦ α_φ, so together they say that these maps are mutually inverse.

**Sums.** Lean's `finsum` is the sum over the support of the summand when that support is finite, and 0 otherwise. In (2), the summand at q is nonzero only when q.out lies in finitely many cosets: for v ∈ I the support of v is compact modulo H⁰, and H⁰\H is discrete because H⁰ is open. In `rationalNormKernelConvolution`, for φ in H(G,ρ), the summand is nonzero only on the finitely many cosets meeting the support of φ. In these cases `finsum` is the finite sum of Renard's formulas. Renard's sums in the convolution and in α_φ are over G/⁰G and ⁰G\G. Because ⁰G is normal these are the same cosets, and the summands depend only on the coset. The Lean sums use the representatives `q.out`, so the statement needs no independence claim.

**Left and right cosets.** Renard's condition (ii) uses left cosets g⁰G. The Lean condition uses the image in H ⧸ H⁰, which is the set of cosets g H⁰. The inverse formula sums over H⁰\H, as Renard's ∑_{ḡ ∈ ⁰G\G} does.

**Universes.** ρ has carrier in `Type uV` and I has carrier in `Type (max uF uV)`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

## Generalization and provenance

Renard proves the Proposition for one irreducible summand ρ of the restriction to ⁰G of an irreducible supercuspidal π. The Lean statement is made for every irreducible smooth representation ρ of H⁰, for every connected reductive G over a nonarchimedean local field. It has no maximal split torus, cocharacter, root system or topological premise and no representation π. So the statement is derived from the source rather than a literal transcription. Its provenance is recorded as derived.

The reason is that Renard's computation uses only the following facts: H⁰ is an open normal subgroup of H, f_w is defined, and every f ∈ V_Π has the finite decomposition (VI.4.2.2). None of these uses π or the supercuspidality of π. In the formalization they hold for every connected reductive G: openness is the published `isOpen_rationalCommonNormKernel`, normality is the published instance, and (VI.4.2.2) holds because the support of f is compact modulo H⁰ and H⁰\H is discrete. Renard's ρ, an irreducible summand of Res π, is in particular an irreducible smooth representation of H⁰, so his Proposition is a special case.

Irreducibility of ρ (finite generation would suffice) is needed for the finite-support condition (ii) on φ_α. If w₀ generates W, then f_{ρ(h)w₀} is the right translate of f_{w₀} by h. Since H⁰ is normal, α(f_{ρ(h)w₀}) has its support in the same finitely many cosets as α(f_{w₀}). So the support of φ_α lies in finitely many cosets. Without finite generation this fails. Take ρ an infinite direct sum of trivial representations of H⁰ with basis (e_n), and choose t ∈ H whose image in the infinite group H/H⁰ has infinite order (such t exists when G has a nontrivial rational character). The endomorphism of I defined by α(f_{e_n}) = r(t⁻ⁿ) f_{e_n} gives a φ_α whose support meets infinitely many cosets, so φ_α is not in H(G,ρ). The statement is therefore not extended to arbitrary ρ.

## Scope

This module defines H(G,ρ) and the convolution, and states the Proposition of VI.4.2 as a Prop-valued target. It does not prove the statement. It also does not formalize the rest of VI.4.2, which makes Hom_G(Π,τ) and Hom_{⁰G}(ρ, Res τ) into right H(G,ρ)-modules. The VI.4.1 statements are the separate modules `RationalSummandSmallProgeneratorStatement` and `RationalSummandHomEquivalenceStatement`. The later results of VI.4 (the structure of R, its center and the center of the block) are not stated here.
