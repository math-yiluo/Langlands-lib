# Continuation of tested intertwining terms with poles along the inverted roots

Module `Langlands.Global.AdelicIntertwiningInvertedRootStatement` defines two notions for a
standard parabolic family and one proposition; it proves nothing.

- `Langlands.Global.StandardParabolicFamily.invertedRoots`: the roots of `A_J` in `U_J`
  inverted by the Weyl element of a normalizer point `n`;
- `Langlands.Global.StandardParabolicFamily.IsInvertedRootRegular`: regularity of a parameter
  for these roots alone;
- `Langlands.Global.IntertwiningInvertedRootCuspidalTestContinuationStatement`: the meromorphic
  continuation of the cuspidal tests of `[M(n, μ) φ']_{nμ}` in `μ ∈ X^*(P_{I'}) ⊗ ℂ`, with poles
  along the hyperplanes of the inverted roots and agreement with the integral wherever `Re μ` is
  regular for the inverted roots.

## Setting

The binders are those of `IntertwiningRestrictedCuspidalTestContinuationStatement` (module
`Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningReduction`, whose Markdown describes
the common setting): a number field `F`, an affine group scheme `G` of finite type over `F`, a
standard parabolic family `𝓕` (standard parabolics `P_J = M_J U_J` with split components `A_J`,
indexed by sets `J` of simple relative roots of one maximal split torus `T`, `𝓕.i : T → G`, and one
generic cocharacter `𝓕.ν`), the instances `Fintype (relativeWeylGroup 𝓕.i)` and
`Mono (𝓕.f J)` used by the root forms, a maximal compact `K` of `G(𝔸)` in good position
(`h₀ : P₀(𝔸) K = G(𝔸)`, `K` maximal compact, `K ∩ M_J(𝔸)` maximal compact in `M_J(𝔸)` for every `J`),
a closed embedding `rho` and a smooth structure `hsmooth`. The positive relative roots
`positiveRelativeRoots 𝓕.i 𝓕.ν` are the relative roots of `T` pairing positively with `𝓕.ν`.

## `invertedRoots`

For a standard index `J` and `n ∈ normalizerPoints 𝓕.i`, `𝓕.invertedRoots J n` is the set of
characters `β` of `A_J` such that

- `β ∈ (𝓕.rootPresentation J).unipotentRoots` (a root of `A_J` in `U_J`: a nonzero restriction
  `χ ∘ f_J` of a positive relative root `χ`, module `Langlands.Global.AdelicEisensteinConvergenceStatement`), and
- `β = χ ∘ f_J` for some positive relative root `χ` such that
  `schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk n) χ` is not a positive relative root.

`schemeWeylCharacterAction` acts by `(n · χ)(x) = χ(n⁻¹ x n)`, which is the action `χ ↦ wχ` of the
Weyl element `w` of `n` in Bernstein–Lapid. Since `n · χ` is again a relative root, "not positive"
means `wχ < 0`. So `invertedRoots J n` consists of the roots of `A_J` in `U_J` represented by a
root `β > 0` with `wβ < 0`. When `(n, c)` presents an element of `W(P_J, P_{J'})`, `n` maps the
roots of `M_J` to roots of `M_{J'}`, so two positive roots with the same restriction to `A_J` have
transports of the same sign; the condition does not depend on the chosen `χ`.

## `IsInvertedRootRegular`

`𝓕.IsInvertedRootRegular J n R μ`, for `μ ∈ X^*(P_J) ⊗ ℂ`, says
`R < (𝓕.rootPresentation J).realRootFunctional hA hT β (parameterRealPart F (𝓕.P J) μ)` for every
`β ∈ 𝓕.invertedRoots J n`, that is `R < B(Re μ|_{A_J}, β)` with the Weyl-induced positive form `B`
on `X^*(A_J) ⊗ ℝ`; here `hA = (𝓕.isCompatible J).splitComponent.isCentralSplitTorus.1.1` and
`hT = 𝓕.maximalSplit.isSplitSubtorus.1`. The predicate
`(𝓕.rootPresentation J).IsRegularParameter hA hT R μ` asks the same inequality for all roots of `A_J`
in `U_J`, so regular parameters are regular for the inverted roots.

## `IntertwiningInvertedRootCuspidalTestContinuationStatement`

Let `I'`, `J` be standard indices, `n ∈ normalizerPoints 𝓕.i` and `c : M_J → M_{I'}` with
`IsWeylConjugation (𝓕.p I') (𝓕.l I') (𝓕.p J) (𝓕.l J) n c` (so `(n, c)` presents an element of
`W(P_{I'}, P_J)`, module `Langlands.Global.AdelicIntertwiningOperator`), `π : P_J → M_J` with
`𝓕.l J ≫ π = 𝟙`, and `φ'` automorphic on `U_{I'}(𝔸) M_{I'}(F) \ G(𝔸)`
(`𝓕.IsAutomorphicOn hsmooth Kinf rho I' φ'`, `Kinf = K.comap (ofInfinite F G)`). The statement
asserts that there are `k : ℕ`, functions `Φ i` on `G(𝔸)`, scalar functions `coeff i` on
`X^*(P_{I'}) ⊗ ℂ` and a set `D` such that

1. every `coeff i` is meromorphic in linear coordinates with domain `D`
   (`IsMeromorphicInCoordinatesOn`);
2. every `coeff i` has poles along the hyperplanes of the root forms
   `(𝓕.rootPresentation I').rootFunctional hA' hT β`, `β ∈ 𝓕.invertedRoots I' n`
   (`HasRootHyperplanePoles`, module `Langlands.Analysis.Meromorphic.RootHyperplanePoles`);
3. there is `R` such that every `μ` with `𝓕.IsInvertedRootRegular I' n R μ` lies in `D`, and for
   every such `μ`, every cusp form `ψ` on `M_J(F) \ M_J(𝔸)` (`𝓕.IsLeviCuspForm Kinf rho J ψ`) and
   every `g`,
   `𝓕.leviPairing J (𝓕.constantTerm J ([M(n, μ) φ']_{nμ})) g ψ =
   ∑ i, coeff i μ * 𝓕.leviPairing J (𝓕.constantTerm J ([Φ i]_{nμ})) g ψ`.

Here `[M(n, μ) φ']_{nμ}` is the intertwining integral
`(𝓕.isIwasawaCompact_of_minimal h₀ I').intertwiningIntegral (𝓕.iU I') (𝓕.iU J ≫ 𝓕.p J) n φ' μ`,
the integral of `φ'_μ(n⁻¹ v g)` over `(U_J(F) ∩ n U_{I'}(𝔸) n⁻¹) \ U_J(𝔸)`; `[Φ i]_{nμ}` is the twist
`(𝓕.isIwasawaCompact_of_minimal h₀ J).parameterTwist (Φ i) (weylParameter (𝓕.l I') c π μ)` by the
height of `P_J` at the parameter `nμ` of `P_J`; and the test is the norm-one Levi pairing of the
constant term along `U_J` with `ψ`, as in `IntertwiningRestrictedCuspidalTestContinuationStatement`.

Compared with `IntertwiningRestrictedCuspidalTestContinuationStatement` in the case `I = I'`, the
pole set is the smaller set of inverted roots, the region of agreement is the larger region of
parameters regular for the inverted roots only, the coefficients are holomorphic on that region,
and no positivity of `n` is assumed.

## Source and derivation

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), 187–234 (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, PDF
and TeX `1911.02342.tex`); C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and
Eisenstein series*, Cambridge University Press, 1995
(`moeglin-waldspurger-1995-spectral-decomposition`).

- Bernstein–Lapid §2.2, p. 191 (TeX lines 431–437): `[M(w, λ)φ]_{wλ}(g)` is the integral of
  `φ_λ(w⁻¹ u g)` over `(wU_Pw⁻¹ ∩ U_Q)(𝔸) \ U_Q(𝔸)`, which converges locally uniformly in `g` and
  `λ` provided that `⟨Re λ, α^∨⟩ ≫ 0` for every root `α ∈ Φ_P` with `wα < 0`.
- Mœglin–Waldspurger II.1.6, Remark and Proposition (i), (iv), pp. 87–88: the integral over
  `(U'(k) ∩ wU(k)w⁻¹) \ U'(𝔸)` equals the integral over `(U'(𝔸) ∩ wU(𝔸)w⁻¹) \ U'(𝔸)`, and it
  converges absolutely and locally uniformly when `⟨Re π, α⟩ ≫ 0` for every root `α > 0` with
  `wα < 0`.
- Bernstein–Lapid Theorem 2.3 (3), p. 191 (TeX lines 458–460): for `w ∈ W(P, Q)`,
  `λ ↦ M(w, λ)φ` takes values in a finite-dimensional space of automorphic forms along `Q` and
  continues meromorphically to `X^*(P) ⊗ ℂ`.
- Bernstein–Lapid §8.6, pp. 225–226 (TeX lines 3517–3523): decomposing `w` into elementary
  symmetries and using multiplicativity, the singularities of `M(w, λ)` are of the form
  `⟨λ, β^∨⟩ = c` with `β ∈ Φ_P`, `wβ < 0`.

Bernstein–Lapid do not state the proposition in this form; it is derived from these items with
`P = P_{I'}`, `Q = P_J`. Choose a basis `Φ i` of the finite-dimensional space of Theorem 2.3 (3),
so that `M(n, μ) φ' = ∑ i, a_i(μ) Φ i`, hence `[M(n, μ) φ']_{nμ} = ∑ i, a_i(μ) [Φ i]_{nμ}`, with
`a_i` meromorphic. By §8.6 the `a_i` are singular only along hyperplanes `⟨μ, β^∨⟩ = c` with `β`
inverted; near each point finitely many of these hyperplanes pass, and a power of the product of
the centered forms clears the `a_i`. The root form `μ ↦ B(μ|_{A_{I'}}, β)` is a nonzero multiple of
`μ ↦ ⟨μ, β^∨⟩` (see the Markdown of `Langlands.Global.AdelicRootHyperplaneStatement`). On the
convex tube where `⟨Re μ, β^∨⟩` is large for the inverted roots the integral converges locally
uniformly (§2.2, MW II.1.6 (iv)), hence is holomorphic there, and it agrees with the continuation
on the smaller region of `P_{I'}`-regular parameters, hence on the whole tube; since the `Φ i` are
linearly independent, the `a_i` are determined there by finitely many values of the integral and
are holomorphic on the tube, which therefore lies in the domain. The tests are linear in the
expansion: the constant term along `U_J` is a linear integral over a compact quotient, and the
pairings with cusp forms converge absolutely by the rapid decay of cusp forms on
`M_J(F) \ M_J(𝔸)^1` (Mœglin–Waldspurger I.2.18) and the moderate growth of automorphic forms.

## Use

`Langlands.Global.intertwiningRestrictedCuspidalTestContinuationReduction` (module
`Langlands.Global.AdelicIntertwiningInvertedRootReduction`) proves that this proposition implies
`IntertwiningRestrictedCuspidalTestContinuationStatement`. The present module does not prove the
proposition.
