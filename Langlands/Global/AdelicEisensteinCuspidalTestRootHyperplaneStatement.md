# Root-hyperplane singularities of the cuspidal tests of Eisenstein series

Module `Langlands.Global.AdelicEisensteinCuspidalTestRootHyperplaneStatement`
states the proposition
`Langlands.Global.EisensteinCuspidalTestRootHyperplaneStatement` and proves
nothing.

## Setting

The binders and hypotheses are those of
`EisensteinRootHyperplaneContinuationStatement` (module
`Langlands.Global.AdelicRootHyperplaneContinuationStatement`), in the same
order. To these are added the instance `LocallyOfFiniteType G.X.hom`, a
standard parabolic family `𝓕 : StandardParabolicFamily F G` (module
`Langlands.Global.AdelicLeadingCuspidalComponents`), and two hypotheses on
`K`:

- `IsIwasawaCompact (𝓕.p ⟨∅, _⟩) K`: `P₀(𝔸) K = G(𝔸)` for the minimal standard
  parabolic `P₀`;
- for every standard index `J`, the inverse image of `K` in `M_J(𝔸)` is a
  maximal compact subgroup of `M_J(𝔸)`.

So `G` is connected reductive over a number field `F`, `p : P → G` is a
parabolic with geometric unipotent radical `iU`, rational Levi `l` and split
component `a`, presented by `r : ParabolicRootPresentation p l a`. `K` is a
maximal compact subgroup of `G(𝔸)` with `P(𝔸) K = G(𝔸)` (`hK`), `rho` is a
closed matrix embedding, and `φ` is an automorphic form on
`U(𝔸) M(F) \ G(𝔸)` for `Kinf = K.comap (ofInfinite F G)` and `rho`. The
parabolic `P` need not be standard for `𝓕`.

## Statement

Write `Kinf = K.comap (ofInfinite F G)`. There are functions
`Γ J ψ g : X^*(P) ⊗ ℂ → ℂ` and sets `D J ψ g ⊆ X^*(P) ⊗ ℂ`, for standard
indices `J`, functions `ψ` on `M_J(𝔸)` and `g ∈ G(𝔸)`, such that:

1. for every `J`, every cusp form `ψ` on `M_J(F) \ M_J(𝔸)`
   (`𝓕.IsLeviCuspForm Kinf rho J ψ`) and every `g`:
   - `Γ J ψ g` is meromorphic in linear coordinates with domain of
     holomorphy `D J ψ g` (`IsMeromorphicInCoordinatesOn`, module
     `Langlands.Analysis.Meromorphic.LinearCoordinates`);
   - for some `R`, whenever `λ` is `R`-regular (`r.IsRegularParameter hA hT R λ`),
     `Γ J ψ g λ = 𝓕.leviPairing J (𝓕.constantTerm J (hK.eisensteinSeries φ λ)) g ψ`,
     the norm-one Levi pairing
     `∫_{M_J(F) \ M_J(𝔸)^1} (C_J E(φ, λ))(ι(m) g) \overline{ψ(m)} dm` of the
     constant term of the Eisenstein series along the standard parabolic `P_J`
     with `ψ`;
2. for every linear coordinate system `e : ℂⁿ ≃ₗ[ℂ] X^*(P) ⊗ ℂ` and every
   `s₀ ∈ ℂⁿ` there are a finite set `S` of roots of `A` in the unipotent
   radical of `P` (`S ⊆ r.unipotentRoots`), an exponent `m` and an open
   `W ∋ s₀` such that for every `J`, every cusp form `ψ` and every `g` some
   function `h`, complex differentiable on `W`, satisfies
   `h s = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀))^m · Γ J ψ g (e s)`
   for all `s ∈ W` with `e s ∈ D J ψ g`.

The continuation `Γ`, its domain and the regularity bound may depend on
`(J, ψ, g)`. Near each point, the root set `S`, the exponent `m` and the
neighbourhood `W` may not.

## Source and correspondence

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein` (PDF in the
registered folder; TeX `1911.02342.tex`):

- §2.1, p.190: `K` is fixed in good position with respect to a minimal Levi
  subgroup, so that `G(𝔸) = M(𝔸) U(𝔸) K` and `M(𝔸) ∩ K` is maximal compact
  for every standard parabolic. Here these are the two hypotheses on `K`
  relative to `𝓕`.
- §6.2, (6.8), p.202: the cuspidal projection along a standard parabolic is
  detected by the pairings of constant terms with cusp forms on
  `M(F) \ M(𝔸)^1`. These are the `𝓕.leviPairing` of `𝓕.constantTerm`.
- Lemma 6.10, (6.17) and (6.18), pp.208–209: the cuspidal part of the constant
  term of `E(φ, λ)` along a standard `Q` is the finite sum
  `∑_{w ∈ W^{⊃Q}(P)} [M(w, λ)(C^cusp_{P,P_w} φ)]_{wλ}`.
- §8.6, pp.225–226 (TeX lines 3517–3530): the singularities of `M(w, λ)` lie
  along hyperplanes `⟨λ, β^∨⟩ = c` with `β ∈ Φ_{P}`, and "the singularities of
  `E(φ, λ)` are precisely those of its cuspidal components … It follows from
  (6.18) that the singularities of `E(φ, λ)` are also along root hyperplanes."

The proposition is the scalar form of the last step: the pairings of the
cuspidal components with cusp forms have their singularities along root
hyperplanes. By (6.18), each pairing is a finite sum over `w` of pairings of
`[M(w, λ)(C^cusp_{P,P_w} φ)]_{wλ}(· g)` with `ψ`. The operator values span a
finite-dimensional space of functions. The coefficients of these values in a
fixed basis carry all the singularities. On `M_J(𝔸)^1` the twist by `wλ`
contributes only the factor `exp⟨wλ, H_J(g)⟩`, which is entire in `λ`. So one
product of root forms clears all the pairings near a point, uniformly in `ψ`
and `g`. A singular hyperplane `⟨λ', β^∨⟩ = c` of `M(w, ·)` on
`X^*(P_w) ⊗ ℂ` meets `X^*(P) ⊗ ℂ` in a translate of the kernel of
`λ ↦ B(λ, β|_A)`, where `β|_A` lies in `r.unipotentRoots`, or, when `β|_A = 0`,
not at all. Near `λ₀` only the hyperplanes through `λ₀` matter; they are the
zero sets of `λ ↦ B(λ - λ₀, β|_A)`. The form `B` is the restriction of an invariant form
on the characters of the maximal split torus, so the source coroot forms are
proportional to `r.rootFunctional hA hT β`.

The local product form with `S`, `m` and `W` independent of the test is the
form of the Corollary in §8.6, and of
`EisensteinRootHyperplaneContinuationStatement`, applied to the cuspidal tests.

## Scope

Only the number field case is stated. The statement concerns the actual
convergent series `hK.eisensteinSeries φ λ` in the regular region and the
continuations of its cuspidal tests. It does not assert the continuation of
`E(φ, λ)` itself or the injectivity of cuspidal tests on automorphic forms.
