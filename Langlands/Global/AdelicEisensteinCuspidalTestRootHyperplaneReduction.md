# Root-hyperplane clearing of cuspidal tests from continued cuspidal expansions

Module `Langlands.Global.AdelicEisensteinCuspidalTestRootHyperplaneReduction`
defines two propositions and proves the second:

- `Langlands.Global.EisensteinCuspidalTestContinuedExpansionStatement`, the
  premise;
- `Langlands.Global.EisensteinCuspidalTestRootHyperplaneReductionStatement`, the
  implication
  `EisensteinCuspidalTestContinuedExpansionStatement → EisensteinCuspidalTestRootHyperplaneStatement`
  (both in universe `u`), proved by
  `Langlands.Global.eisensteinCuspidalTestRootHyperplaneReduction`.

The target `EisensteinCuspidalTestRootHyperplaneStatement` is published in the
module `Langlands.Global.AdelicEisensteinCuspidalTestRootHyperplaneStatement`.
This module does not prove the premise.

It also proves three facts about a standard parabolic family
`𝓕 : StandardParabolicFamily F G` (module
`Langlands.Global.AdelicLeadingCuspidalComponents`):

- `StandardParabolicFamily.isClosedImmersion_p`: every `𝓕.p J` is a closed
  immersion. It is used as a local instance in this file, so that the Iwasawa
  heights and twists of the standard parabolics can be formed.
- `StandardParabolicFamily.isIwasawaCompact_of_minimal`: if
  `P₀(𝔸) K = G(𝔸)` for the minimal standard parabolic `P₀ = 𝓕.p ⟨∅, _⟩`, then
  `P_J(𝔸) K = G(𝔸)` for every standard `J`. Since `P₀ ⊆ P_J`
  (`𝓕.le_iff_range_le`), `P₀` factors through `P_J`
  (`SubgroupFunctor.rangeFactor_comp`), and `IsIwasawaCompact.of_comp` applies.
- `StandardParabolicFamily.finite_standardIndex_of_finite_simpleRoots`: there are finitely many
  standard indices, since there are finitely many simple relative roots.

## The premise

`EisensteinCuspidalTestContinuedExpansionStatement` has the binders and the
hypotheses of `EisensteinCuspidalTestRootHyperplaneStatement`, in the same
order. So `G` is connected reductive over a number field `F`, `p : P → G` is a
parabolic with geometric unipotent radical `iU`, rational Levi `l` and split
component `a : A → M`, presented by `r : ParabolicRootPresentation p l a`, `𝓕` is
a standard parabolic family, `K` is a maximal compact subgroup of `G(𝔸)` with
`P(𝔸) K = G(𝔸)` (`hK`), in good position for `𝓕`, `rho` is a closed matrix
embedding, and `φ` is automorphic on `U(𝔸) M(F) \ G(𝔸)`. The parabolic `P`
need not be standard for `𝓕`. Write `Kinf = K.comap (ofInfinite F G)`.

The assertion: for every standard index `J` and every proof `hKJ` of
`IsIwasawaCompact (𝓕.p J) K` there are `k : ℕ`, functions
`Φ i : G(𝔸) → ℂ`, complex linear maps
`L i : X^*(P) ⊗ ℂ → X^*(P_J) ⊗ ℂ`, scalar functions
`c i : X^*(P) ⊗ ℂ → ℂ` (`i : Fin k`) and a set `D ⊆ X^*(P) ⊗ ℂ` such that

1. every `c i` is meromorphic in linear coordinates with domain of holomorphy
   `D` (`IsMeromorphicInCoordinatesOn`, module
   `Langlands.Analysis.Meromorphic.LinearCoordinates`);
2. every `c i` has poles along the hyperplanes of the root forms:
   `HasRootHyperplanePoles (r.rootFunctional hA hT) r.unipotentRoots (c i) D`
   (module `Langlands.Analysis.Meromorphic.RootHyperplanePoles`). That is, for
   every linear coordinate system `e : ℂⁿ ≃ₗ[ℂ] X^*(P) ⊗ ℂ` and every `s₀`
   there are a finite set `S` of roots of `A` in the unipotent radical of `P`,
   an exponent `m`, an open `W ∋ s₀` and a function `h` complex differentiable
   on `W` with `h s = (∏ β ∈ S, B(e s - e s₀, β))^m · c i (e s)` for `s ∈ W` with
   `e s ∈ D`. Here `B(·, β)` is `r.rootFunctional hA hT β` (module
   `Langlands.Global.AdelicRootHyperplaneStatement`);
3. there is `R` such that for every `R`-regular `λ`
   (`r.IsRegularParameter hA hT R λ`), every cusp form `ψ` on
   `M_J(F) \ M_J(𝔸)` (`𝓕.IsLeviCuspForm Kinf rho J ψ`) and every `g ∈ G(𝔸)`,

   `𝓕.leviPairing J (𝓕.constantTerm J (hK.eisensteinSeries φ λ)) g ψ =
     ∑ i, c i λ * 𝓕.leviPairing J (𝓕.constantTerm J (hKJ.parameterTwist (Φ i) (L i λ))) g ψ`.

   The left side is the norm-one Levi pairing
   `∫_{M_J(F) \ M_J(𝔸)^1} (C_J E(φ, λ))(m g) \overline{ψ(m)} dm` of the
   constant term of the convergent Eisenstein series along `P_J`. On the right,
   `hKJ.parameterTwist Φ μ` is the twist `[Φ]_μ(x) = Φ(x) m_{P_J}(x)^μ` by the
   Iwasawa height of `P_J` for `K`.

The hypothesis `hKJ` only serves to form the twist. It follows from the good
position of `K` (`isIwasawaCompact_of_minimal`). As propositions have at most
one proof, the quantifier over `hKJ` adds no condition.

## Source and derivation of the premise

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein` (journal PDF in the
registered folder, TeX `1911.02342.tex`):

- §6.2, (6.8), p.202: the cuspidal projection `φ ↦ φ^cusp` along a standard
  parabolic is characterized by the pairings with cusp forms on
  `M(F) \ M(𝔸)^1`. These pairings are the `𝓕.leviPairing` of the
  `𝓕.constantTerm`.
- §6.10, Lemma, (6.17) and (6.18), p.208 (TeX lines 1728–1742): for
  `λ` in the range of convergence,
  `C^cusp_{G,Q} E(φ, λ) = ∑_{w ∈ W^{⊃Q}(P)} [M(w, λ)(C^cusp_{P,P_w} φ)]_{wλ}`.
- Theorem 2.3 (3), p.191, and the Lemma of §8.2, p.222 (TeX lines 3274–3290):
  the values `M(w, λ)φ'` lie in a finite-dimensional subspace of automorphic
  forms, independent of `λ`, and `λ ↦ M(w, λ)φ'` continues meromorphically.
- §8.6, pp.225–226 (TeX lines 3517–3530): the singularities of `M(w, λ)` are
  of the form `⟨λ, β^∨⟩ = c` with `β` a root in the unipotent radical of the
  source parabolic and `wβ < 0`, and "it follows from (6.18) that the
  singularities of `E(φ, λ)` are also along root hyperplanes".

The premise is derived from these items; Bernstein–Lapid do not state it
separately. For a standard `P` and `Q = P_J`, (6.18) and (6.8) give, for
regular `λ`,
`(C_J E(φ, λ)(· g), ψ) = ∑_w ([M(w, λ)(C^cusp_{P,P_w} φ)]_{wλ}(· g), ψ)`. For
each `w`, a basis `Φ_{w,i}` of the finite-dimensional space containing the
values `M(w, λ)(C^cusp_{P,P_w} φ)` gives
`M(w, λ)(C^cusp_{P,P_w} φ) = ∑_i c_{w,i}(λ) Φ_{w,i}` with meromorphic
coefficients `c_{w,i}`, and `[Φ_{w,i}]_{wλ}` is the twist by
`L_{w,i} λ = wλ`, a linear function of `λ`. The singular hyperplanes of the
coefficients are of the form `⟨λ, β^∨⟩ = c`, where `β` is a root in the
unipotent radical of `P_w` with `wβ < 0`. Such a `β` does not lie in `M_P`:
the elements `w` of `W^{⊃Q}(P)` satisfy `wα > 0` for the simple roots `α` of
`M_P` (§6.7, p.207), so they map the positive roots of `M_P` to positive roots.
So `β` restricts to a root of `A` in the unipotent radical of `P`. On `X^*(P) ⊗ ℂ` the form `⟨λ, β^∨⟩` is a nonzero multiple of
`B(λ|_A, β|_A)`, as explained in the Markdown of
`AdelicRootHyperplaneStatement`. Near `λ₀` only the hyperplanes through `λ₀`
matter, and a power of the product of the forms `λ ↦ B(λ - λ₀, β)` clears the
coefficients, as in the Corollary of §8.6. The functions `Φ_{w,i}` are left
`U_J(𝔸)`-invariant, so the constant term along `P_J` of a twist is the twist
itself. The statement keeps only what is needed below: it does not require the
`Φ i` to be automorphic, nor the `L i` to be Weyl transports.

For a parabolic `P` that is not standard, choose `γ ∈ G(F)` with
`P' = γ P γ⁻¹` standard. The height `H_P` for `K` is right `K`-invariant, so
`φ_λ(γ⁻¹ y) = e^{⟨λ, H_P(γ⁻¹)⟩} · (φ(γ⁻¹ ·))_{γλ}(y)` for the height of `P'`,
and `E_P(φ, λ) = e^{⟨λ, H_P(γ⁻¹)⟩} E_{P'}(φ(γ⁻¹ ·), γλ)`. The exponential factor
is entire in `λ` and goes into the coefficients, and the root forms of `P` and
`P'` correspond under conjugation by `γ`.

## Proof of the implication

`eisensteinCuspidalTestRootHyperplaneReduction` takes the premise and the data
of the target.

1. `X^*(P) ⊗ ℂ` is finite-dimensional (`exists_complexParameterEquiv`), and
   `K` has Iwasawa coverage for every `P_J` (`isIwasawaCompact_of_minimal`).
2. The premise, applied for each standard `J`, gives `k J`, `Φ J`, `L J`,
   `c J`, `D J` and `R J`.
3. The common domain. Let `Dc = ⋂_{(J, i)} D J`, the intersection over the
   finite type `Σ J, Fin (k J)` (`finite_standardIndex_of_finite_simpleRoots`). It is open and dense
   in every linear coordinate system, because each `D J` with `k J > 0` is the
   domain of holomorphy of some `c J i`, and a finite intersection of open
   dense sets is open and dense. Every `c J i` is meromorphic in coordinates
   with domain `Dc` (`IsMeromorphicInCoordinatesOn.congr_mono`) and has poles
   along the root hyperplanes on `Dc` (`HasRootHyperplanePoles.mono`).
4. The continued tests. Put
   `Γ J ψ g λ = ∑ i, c J i λ · ((C_J Φ_{J,i})(· g), ψ) · m_{P_J}(g)^{L_{J,i} λ}`
   and `D J ψ g = Dc`.
   - Meromorphy: in coordinates `e`, the `i`-th term is `c J i ∘ e`, meromorphic
     with domain `e⁻¹ Dc`, times the entire function
     `s ↦ ((C_J Φ_{J,i})(· g), ψ) · exp⟨L_{J,i}(e s), H_{P_J}(g)⟩`.
     `IsMeromorphicOn.mul` and `IsMeromorphicOn.sum` (module
     `Langlands.Analysis.Meromorphic.ScalarIdentity`) give meromorphy of the
     sum with domain `e⁻¹ Dc`.
   - Agreement: for `R J`-regular `λ`, the premise and
     `StandardParabolicFamily.leviPairing_constantTerm_parameterTwist` (module
     `Langlands.Global.AdelicStandardConstantTermTwist`, applied with `P = J`)
     give `Γ J ψ g λ = (C_J E(φ, λ)(· g), ψ)`: on `M_J(𝔸)^1` the twist only
     contributes the factor `m_{P_J}(g)^{L_{J,i} λ}` at the external argument.
   - Clearing: for coordinates `e` and a point `s₀`,
     `exists_rootPoleData_family` (module
     `Langlands.Analysis.Meromorphic.RootHyperplanePoles`), applied to the finite
     family `c J i` indexed by `Σ J, Fin (k J)` on `Dc`, gives one finite set
     `S ⊆ r.unipotentRoots`, one exponent `m`, one open `W ∋ s₀` and numerators
     `h_{J,i}` complex differentiable on `W`. For every `J`, every cusp form `ψ`
     and every `g`, the function
     `s ↦ ∑ i, h_{J,i}(s) · ((C_J Φ_{J,i})(· g), ψ) · m_{P_J}(g)^{L_{J,i}(e s)}`
     is complex differentiable on `W` and equals
     `(∏ β ∈ S, B(e s - e s₀, β))^m · Γ J ψ g (e s)` for `s ∈ W` with
     `e s ∈ Dc`.

The set `S`, the exponent `m` and the neighbourhood `W` are chosen before `J`,
`ψ` and `g`, as the target requires.

## Scope

Only the number field case is stated. The module proves the implication and
the three facts about standard families. It does not prove
`EisensteinCuspidalTestContinuedExpansionStatement`.
