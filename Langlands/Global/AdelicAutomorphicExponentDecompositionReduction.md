# The exponent decomposition from Harish-Chandra's finiteness theorem

Module `Langlands.Global.AdelicAutomorphicExponentDecompositionReduction` proves
`Langlands.Global.AutomorphicExponentDecompositionReductionStatement` (module
`Langlands.Global.AdelicAutomorphicExponentDecompositionReductionStatement`) as
`Langlands.Global.automorphicExponentDecompositionReduction`: Harish-Chandra's finiteness theorem
on parabolic quotients, `ParabolicHarishChandraFinitenessStatement`, implies
`AutomorphicExponentDecompositionStatement`. The module does not prove the finiteness theorem.
On the way it proves, with no hypothesis on a compact subgroup,
`StandardParabolicFamily.exists_exponentDecomposition_of_finiteDimensional_translates`: an
automorphic function on `U_J(𝔸) M_J(F) \ G(𝔸)` whose left translates by the positive split
component `𝔄_J` span a finite-dimensional space has the exponent decomposition.

## Results

In namespace `Langlands.Automorphic.GroupSchemeFunctions`:

- `centerAnnihilation_leftTranslate`: an ideal of the center annihilating every infinite slice of
  `φ` annihilates every infinite slice of `x ↦ φ(a x)`, for every `a ∈ G(𝔸)`. The infinite slice
  of the translate at `b` is the left translate by `a_∞` of the slice of `φ` at `a_f b`, and the
  enveloping-algebra action commutes with left translation by
  `Langlands.Automorphic.GroupSchemeFunctions.plotSmoothEnvelopingAction_leftTranslation`
  (module `Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation`).
- `Langlands.Global.exists_finiteDimensional_profile` gives one finite-dimensional space containing the functions `k ↦ φ(g k)` on `K_∞` for all `g`. A basis for the span of the right translates gives finitely many coefficient functions on `K_∞` that span such a space.

In namespace `Langlands.Global`, for a `ℤ`-basis `b` of the rational characters `X^*(P)`:

- `basisCoordinateDual b t ∈ RealCharacterDual F P = Hom(X^*(P), ℝ)` has the coordinates `t` in
  the dual basis (`basisCoordinateDual_basis`); it is additive and continuous in `t`, and
  `basisCoordinateDual b (fun j => H (b j)) = H` (`basisCoordinateDual_eval`).
- `basisCoordinates b H = (H (b j))_j` as a real-linear map.
- `basisParameter b μ = ∑ j, μ j ⊗ b j ∈ ℂ ⊗[ℤ] X^*(P)` (the Library's
  `ComplexCharacterParameter`, with the complex scalars as first factor), with
  `⟨basisParameter b μ, H⟩ = ∑ j, H (b j) μ j` (`complexParameterPairing_basisParameter`);
  `basisParameter b` is injective.

In namespace `Langlands.Global.StandardParabolicFamily`, for a compatible standard parabolic
family `fam`:

- `isIwasawaCompact_of_minimal`: `P₀(𝔸) K = G(𝔸)` for the minimal standard parabolic gives
  `P_J(𝔸) K = G(𝔸)` for every standard `J`, since `P₀ ⊆ P_J`.
- `isIso_subgroupMultiplication_levi_radical`: `M_J × U_J → P_J` is an isomorphism, by
  `Dynamic.isIso_subgroupMultiplication` for the split-component cocharacter of the presentation
  (as in `ParabolicRootPresentation.isIso_subgroupMultiplication_of_radical`).
- `exists_positiveSplitComponent_section`: a continuous homomorphism
  `σ : Hom(X^*(P_J), ℝ) → P_J(𝔸)` with values in `𝔄_J` and `σ(H_{P_J}(x)) = x` for `x ∈ 𝔄_J`,
  namely `PositiveRealTorus.logSection` (module `Langlands.Global.AdelicLogSection`); the finite
  index of the restriction of characters to `A_J` is obtained as in
  `Langlands.Global.eisensteinPositiveParameters`.
- `exists_exponentDecomposition_of_finiteDimensional_translates`, stated above.

In namespace `Langlands.Global`:

- `StandardParabolicFamily.exists_exponentDecomposition_of_parabolicHarishChandraFiniteness`:
  given `ParabolicHarishChandraFinitenessStatement`, a maximal compact subgroup `K` of `G(𝔸)` with
  `P₀(𝔸) K = G(𝔸)` for the minimal standard parabolic `P₀`, a closed matrix embedding `rho`, a
  standard `Q` and a function `ψ` automorphic on `U_Q(𝔸) M_Q(F) \ G(𝔸)` for
  `K_∞ = K.comap (ofInfinite F G)`, the function `ψ` has the exponent decomposition of
  `AutomorphicExponentDecompositionStatement`. There is no hypothesis on the intersections of `K`
  with the standard Levis.
- `automorphicExponentDecomposition_of_parabolicHarishChandraFiniteness`: the implication, a
  specialization of the previous theorem; and `automorphicExponentDecompositionReduction`, the same
  term as a proof of `AutomorphicExponentDecompositionReductionStatement`.

## Proof of the decomposition from a finite-dimensional orbit

Let `ψ` be automorphic on `U_J(𝔸) M_J(F) \ G(𝔸)` with finite-dimensional span of
`{ψ(a ·) : a ∈ 𝔄_J}`. The rational characters of `P_J` form a free `ℤ`-module of finite rank
(`ParabolicRootPresentation.rationalCharacters_free_finite`); fix a basis `b` indexed by `κ`.
Then `t ↦ σ(basisCoordinateDual b t)` is a continuous homomorphism `ℝ^κ → 𝔄_J`, and composing with
the left action `splitComponentRepresentation` gives an action `T` of `ℝ^κ` on functions on
`G(𝔸)`. Let `W` be the span of the `T t ψ`; it lies in the span of the `𝔄_J`-translates, so it is
finite-dimensional, and it is `T`-invariant. Its elements are continuous (finite combinations of
translates of the continuous `ψ`), so the orbit maps `t ↦ (T t w)(g)` are continuous. By
`exists_exponentPolynomial_decomposition` (module
`Langlands.Global.FiniteTranslationExponentPolynomials`), `ψ = ∑_{μ ∈ s} u μ` with `u μ ∈ W` and
`t ↦ (T t (u μ))(g) exp(-∑ t j μ j)` a polynomial of degree at most `n`. The exponents are
`λ = basisParameter b μ`, and `c λ = u μ` (well defined since `basisParameter b` is injective).

- Automorphy: every `T t ψ` lies in the submodule `automorphicFunctionsOn` of automorphic
  functions on the quotient, by `StandardParabolicFamily.IsAutomorphicOn.unnormalizedAction`
  (module `Langlands.Global.AdelicSplitComponentShifts`): a left translate by a point of `𝔄_J` of
  an automorphic function on `U_J(𝔸) M_J(F) \ G(𝔸)` is automorphic on the same quotient. Hence `W`
  consists of automorphic functions.
- Exponent: for `x ∈ 𝔄_J` put `t = basisCoordinates b (H_{P_J}(x))`. Then
  `σ(basisCoordinateDual b t) = σ(H_{P_J}(x)) = x`, so `(T t (u μ))(g)` is `(u μ)(x g)`, and
  `x^{-λ} = exp(-⟨λ, H_{P_J}(x)⟩) = exp(-∑ t j μ j)`. Hence `(u μ)(x g) x^{-λ}` is the polynomial
  above composed with the linear map `basisCoordinates b`, evaluated at `H_{P_J}(x)`
  (`comp_linearMap_mem_polynomialFunctions`): this is `HasUnnormalizedExponent J λ (u μ)`.
- Cuspidality: let `Q' < J` and suppose `C_{Q'} ψ = 0`. The constant term along `Q'` is linear on
  automorphic functions on the `J`-quotient (`constantTermLinear`), and
  `C_{Q'}(ψ(a ·)) = (C_{Q'} ψ)(a ·) = 0` for `a ∈ 𝔄_J`
  (`constantTerm_unnormalizedAction_of_radicalInvariant`, using the left `U_J(𝔸)`-invariance of
  `ψ`, which `StandardParabolicFamily.isParabolicGeneratorInvariant_of_isLeftInvariantUnder` of
  `Langlands.Global.AdelicSplitComponentShifts` extracts from the left invariance under
  `U_J(𝔸) M_J(F)`). So `W` lies in the image of the kernel of `constantTermLinear`, and `C_{Q'}(u μ) = 0`.

## Proof of the implication

Assume `ParabolicHarishChandraFinitenessStatement` and let `fam`, `K`, `rho`, `Kinf` and `ψ` be as
in `StandardParabolicFamily.exists_exponentDecomposition_of_parabolicHarishChandraFiniteness`. By the previous paragraph it suffices to show that
the span of the `𝔄_Q`-translates of `ψ` is finite-dimensional. Apply the finiteness theorem to the
parabolic `P_Q` with radical `U_Q` and Levi `M_Q` (parabolic, radical and Levi fields of the
family, `isIso_subgroupMultiplication_levi_radical`), the compact `K` (maximal, with
`P_Q(𝔸)K = G(𝔸)` by `isIwasawaCompact_of_minimal`), the ideal `J` annihilating the slices of `ψ`
(from `IsCenterFiniteFunction`), the open level `L` of `ψ` (from `IsAdelicSmoothFunction`) and the
space `E` of `exists_finiteDimensional_profile`. Every translate `ψ(a ·)`, `a ∈ 𝔄_Q`,
belongs to the resulting finite-dimensional span: it is automorphic on the same quotient, right
invariant under `L` (left and right translations commute), annihilated by `J`
(`centerAnnihilation_leftTranslate`), and `k ↦ ψ(a g k)` is the function of `E` attached to the
point `a g`. The implication `automorphicExponentDecomposition_of_parabolicHarishChandraFiniteness`
applies this theorem to the data of `AutomorphicExponentDecompositionStatement` and discards the
hypotheses that the inverse images of `K` in the standard Levis are maximal compact.

## Sources

The route follows Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.2.17, printed pp. 37–38 (finiteness theorem on `U(𝔸)M(k) \ G`), I.3.1, printed pp. 40–41, and
the Lemma of I.3.2 with its proof, printed pp. 41–43, where the components of an automorphic form
are obtained from its finiteness under `A_M`; the cuspidal case is I.3.3, printed pp. 43–45. The
decomposition is (6.10) of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §6.3, p. 203, with the polynomial description of (6.3)
and the cuspidal decomposition (6.6), §6.2, pp. 201–202. The Lean proof replaces the
`𝔷(A_M)`-action of Mœglin–Waldspurger by the finite-dimensional continuous representation of
`𝔄_Q` on the span of translates and the exponential of its generators.
