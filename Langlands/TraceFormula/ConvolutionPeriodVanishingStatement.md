# Convolution period vanishing

`Langlands.TraceFormula.ConvolutionPeriodVanishingStatement` states that a right
convolution has an integrable and vanishing period along a specified subgroup.

## Setting

Let `G : Type u` be a Hausdorff, locally compact, second-countable topological
group with its Borel σ-algebra. Let `Γ ≤ G` be discrete in its subspace topology,
and let `N ≤ G` be closed. Write `H = Γ ∩ N` as a subgroup of `N`
(`Γ.subgroupOf N` in Lean). The quotient `H \ N` is the Library's
`Langlands.QuotientIntegration.LeftQuotient H` with its quotient topology and
Borel σ-algebra. Write `H n` for the class of `n`, given by `Quotient.mk _ n`.

Take explicit left Haar measures `μG` on `G` and `μN` on `N`, both of which are
also right invariant. Take a measure `νN` on `H \ N` satisfying
`Langlands.QuotientIntegration.IsCompatible H μN Measure.count νN`. This means
`νN` is nonzero, regular and invariant under right translation. With counting
measure on `H`, the coset average of each continuous compactly supported
`h : N → ℂ` is `νN`-integrable and its quotient integral equals
`∫_N h(n) dμN(n)`.

## Statement

Assume `H \ N` is compact. Take `f : C_c(G, ℂ)` such that

`∫_N f(a n b) dμN(n) = 0` for all `a, b ∈ G`.

Take `φ : G → ℂ` with `LocallyIntegrable φ μG` and `φ(γ g) = φ(g)` for all
`γ ∈ Γ` and `g ∈ G`. For every `x ∈ G` and every `P : H \ N → ℂ` satisfying

`P(H n) = ∫_G f(g) φ(n x g) dμG(g)` for all `n ∈ N`,

the conclusion is `Integrable P νN ∧ ∫ q, P q ∂νN = 0`. The right side of the
equation for `P` is `R(f)φ(n x)`, where the right convolution is given by
`R(f)φ(y) = ∫_G f(g) φ(y g) dμG(g)`. All integrals are Bochner integrals.

## Source and derivation

This is a derived statement of the unfolding step in Getz–Hahn. The source
takes `f = f_v ⊗ f^v` with `f_v` supercuspidal at a finite place and
`φ ∈ L²([G])`. For the unipotent radical `N` of each proper rational parabolic,
the proof unfolds the period over `N(F) \ N(𝔸_F)` until the inner integral
is the integral of `f(x⁻¹ n⁻¹ g)` over `N(𝔸_F)`. Local supercuspidality provides
the cancellation in that integral, yielding the source's cuspidal image
conclusion. The registered source is `getz-hahn-2024-automorphic-representations`.
[Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §16.4, Definition 16.4.1 and Lemma 16.4.2 with its proof, printed p. 430 (PDF p. 438)](https://link.springer.com/chapter/10.1007/978-3-031-41153-3_16)

The abstract statement takes the cancellation along `a N b` as its hypothesis
on `f`, and uses a left `Γ`-invariant, locally integrable `φ`. The conclusion
gives absolute convergence and vanishing of the period for the chosen closed
subgroup `N` at every `x`.
