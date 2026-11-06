# The character decay on the opposite chart from the relative root system

Lean module: `Langlands.Representation.Plancherel.ParabolicCharacterDecayProof`,
namespace `Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. This module completes the decay estimate in Waldspurger's proof of the
convergence of the standard intertwining integrals (*La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra* (2003), IV.1.1, printed pp. 277–281), in the form
`ParabolicCharacterDecayInput` of the Library module
`Langlands.Representation.Plancherel.ParabolicIntertwiningDecayAssembly`. It derives two of the
three named inputs of that module from two structural statements:

- `RelativeRootSystemStatement` (the relative roots of a maximal split torus form a root
  system), and
- `CentralSplitTorusCharacterStatement` (central split tori detect nonzero rational characters
  of connected reductive groups).

The third input, finite-length moderate growth, follows from coefficientwise moderate growth
(`RationalCoefficientModerateGrowthStatement`, Waldspurger I.4.4) by the Library's
`rationalFiniteLengthModerateGrowth_of_coefficientGrowth`. So
`ConditionalParabolicIntertwiningStatement` follows from these three statements
(`conditionalParabolicIntertwiningStatement_of_statements`). None of the three statements is
proved here; they are explicit premises.

The argument assembles Library results: the logarithm vectors of
`Langlands.Representation.Plancherel.SplitComponentLogarithm`, the bounds of
`Langlands.Representation.Plancherel.ParabolicLeviLogarithmBounds`, and the conic decay
`exists_parabolicRootCone_decay` of `Langlands.Representation.Plancherel.ParabolicRootCone`.
It is not transcribed from the source.

## Setting and notation

- `F` is a nonarchimedean local field with normalized absolute value `|·|`. For an affine group
  scheme `G` over `Spec F`, `G(F) = rationalPoints G` has the topology
  `rationalPointTopology F G.X`.
- `r : ParabolicRootPresentation p l a` and `r' : ParabolicRootPresentation p' l' a` present two
  parabolics with a common Levi (`hLevi : l ≫ p = l' ≫ p'`). They have geometric unipotent
  radicals `n`, `n'` with point subgroups `Upt` and `U'pt` (`hUpt`, `hU'pt`), and `q` represents
  the opposite parabolic of `r'` with radical `v`. `λ = r.splitComponentCocharacter` and
  `λ' = r'.splitComponentCocharacter`.
- `h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt` gives the Levi
  projection, and `hU` says `Upt` is closed. `parabolicLeviHalfModulus r h hU : M(F) →* ℂˣ` is
  the half modulus `δ_P^{1/2}` transported to `M(F)`.
- `SplitTorus.normalizedRealPart hA χ ∈ Vstar A` is the Library's normalized real part of a
  character `χ` of `A(F)`. `B` is the Weyl-induced character form
  `weylInducedCharacterForm … r.data.f r.data.i`.
- `ParabolicOppositeCharacterDecay r h hU K ρ₀ C` is the Library's statement that for every
  `s` there is `R` such that, along every section `σ` of `(Upt ∩ U'pt) \ U'pt` with values in
  `Ū(F)`, the weights `‖δ_P^{1/2}(m)‖ ‖χ(m)‖` at the Levi components `m` of the Iwasawa
  decompositions `σ(q) = p κ` are bounded by a constant times `‖σ q‖_{ρ₀} ^ (-s)`, locally
  uniformly in `χ ∈ C R`.

## Declarations

- `exp_le_of_cone_height hsp hs hC₃ hX hcone hψ hheight`: real numbers `H, h, K, s', s, C, X,
  y` and `D : ℕ` with `0 ≤ s'`, `s ≤ s'`, `C > 0`, `X ≥ 1`. If
  `H ≤ -(s' D) |h| + K`, `log y = h` and `X ≤ C · max 1 y⁻¹ ^ D`, then
  `exp H ≤ exp (K + s' log C) · X ^ (-s)`.
- `exists_isClosedSubgroup_fin_succ G`: a smooth connected affine group `G` locally of finite
  type over a field has a closed matrix representation on `Fin (N + 1)` for some `N`.
- `parabolicHalfModulusRealPart r h hU : Vstar A` (definition): the normalized real part of
  `parabolicLeviHalfModulus r h hU` composed with `a(F)`, that is, the vector `ρ_P` with
  `log ‖δ_P^{1/2}(m)‖ = ⟨ρ_P, w⟩` for every logarithm vector `w` of `m`.
- `parabolicOppositeCharacterDecay_of_statements r r' hLevi hn hn' hQ hv hUpt hU'pt hRS hS hG
  h hU K hK ρ₀ hρ₀`: for connected reductive `G`, under `RelativeRootSystemStatement` and
  `CentralSplitTorusCharacterStatement`, for every compact open subgroup `K` and every closed
  representation `ρ₀` on a nonempty `Fin N`. The instance hypotheses are those of the host
  setting: `G(F)` is locally compact, nonarchimedean and Hausdorff, the maps
  `r.data.i : T → G` (the maximal split torus) and `r.data.f : A → T` are monomorphisms of
  underlying schemes, and the relative Weyl group of `T` is finite. Under these hypotheses,
  `ParabolicOppositeCharacterDecay r h hU K ρ₀ (parabolicPointUnramifiedIntertwiningRegion r B n q v)`.
- `parabolicCharacterDecayInput_of_statements hRS hS : ParabolicCharacterDecayInput`.
- `parabolicSquaredModulusInput_of_statements hRS hS : ParabolicSquaredModulusInput`. This is
  the Library's `parabolic_squaredModulusCompatibility_of_structural` over the binders of the
  input.
- `conditionalParabolicIntertwiningStatement_of_statements hcoeff hRS hS :
  ConditionalParabolicIntertwiningStatement`, for
  `hcoeff : RationalCoefficientModerateGrowthStatement`.

## Proof outline

- *Real inequality.* `log max(1, y⁻¹) ≤ |log y| = |h|`, so the height bound gives
  `log X ≤ log C + D |h|`. Multiplying by `s' ≥ 0` and using the cone bound gives
  `H ≤ K + s' log C − s' log X`. Exponentiating, `exp H ≤ exp(K + s' log C) X^{−s'}`, and
  `X^{−s'} ≤ X^{−s}` since `X ≥ 1` and `s ≤ s'`.
- *Closed representation.* `Chevalley.exists_line_stabilizer` for the identity subgroup
  `kernelUnit G` gives `ρ` on `Fin (n + 1)` and `e_j` such that, on every test scheme, `x` is
  the identity exactly when `ρ(x) e_j ∈ (units) e_j` (`range_kernelUnit`). If
  `ρ(x) = ρ(y)` then `ρ(x⁻¹ y) = 1` fixes `e_j`, so `x = y`. Thus `ρ` is a monomorphism, and
  `HomImage.isClosedSubgroup_of_mono` makes it closed.
- *Decay.* Fix `s` and put `s' = max s 0`.
  1. For each `m' ∈ M(F)`, `exists_splitComponentLogarithm` gives a logarithm vector `w(m')`.
     Its injectivity premise is `characterRestrict_injective_of_centralSplitTorusCharacter hS`.
     Write `H_{m'} = ⟨·, w(m')⟩`.
  2. `exists_parabolicLineCharacter_rationalMatrixNorm_le` for `λ ∘ a ∘ l ∘ p` gives a line
     character `ξ` of the represented parabolic and `C₃ > 0`, `D`. Restrict `ξ` to `M` through
     the factorization of `l ≫ p`, and let `ψ` be its image `1 ⊗ (ξ|_A)` in `Vstar A`.
  3. For each `mu` admissible for `(λ, λ')`, `exists_positiveWeightLine_le_abs` (with
     `Z(λ' ∘ a ∘ l ∘ p) = M = Z(λ ∘ a ∘ l ∘ p)` from the two Levi equalities) gives a character
     of `M` restricting to `positiveWeightCharacter mu`, and `C_mu > 0`. Put
     `c(mu) = −log C_mu` for admissible `mu` and `c(mu) = 0` otherwise.
  4. Apply `exists_parabolicRootCone_decay` to `λ, λ', c, ψ` and `s' D` to get `R₀, K₀`. Take
     `R = R₀ + S_δ`, where `S_δ = ∑_α |B(ρ_P, α)|` over the relative roots and
     `ρ_P = parabolicHalfModulusRealPart r h hU`.
  5. For `χ₀ ∈ C R`, the neighbourhood is `C R ∩ {χ : ∑_α |B(ν_χ, α)| < S₀ + 1}`. Here
     `ν_χ` is the normalized real part of `χ` on `A`, and `S₀` is the sum at `χ₀`. It is open
     by `isOpen_parabolicPointUnramifiedIntertwiningRegion` and the continuity of
     `χ ↦ B(ν_χ, α)` (`SplitTorus.continuous_normalizedRealPart_apply`). The constant is
     `exp(K₁ + s' log C₃)` with `K₁ = max(K₀, 0)(2 + S₀ + S_δ)`.
  6. For `σ(q) = x = p κ` with Levi component `m` and `m' ∈ M(F)` its preimage:
     - the first clause of the logarithm vector, with the lower bounds of step 3, gives
       `−c(mu) ≤ H_{m'}(positiveWeightCharacter mu)`;
     - `abs_rationalCharacterEval_projection_eq_one` gives `H_{m'}(ξ_G|_A) = 0` for rational
       characters `ξ_G` of `G`;
     - the second clause gives `log ‖δ_P^{1/2}(m)‖ = H_{m'}(ρ_P)` (unramified by
       `rationalCommonNormKernel_le_ker_parabolicLeviHalfModulus`) and
       `log ‖χ(m)‖ = H_{m'}(ν_χ)`.
  7. The region condition of the cone theorem holds for `ν = ν_χ + ρ_P`, because
     `B(ν, α) = B(ν_χ, α) + B(ρ_P, α) > R₀ + S_δ − |B(ρ_P, α)| ≥ R₀`. The size term satisfies
     `∑ |B(ν, α)| ≤ ∑ |B(ν_χ, α)| + S_δ < S₀ + 1 + S_δ`, so the cone theorem gives
     `H_{m'}(ν) ≤ −s' D |H_{m'}(ψ)| + K₁`.
  8. The height bound of step 2 at `q = g(m')` reads `‖x‖ ≤ C₃ max(1, |ξ(q)|⁻¹)^D` with
     `log |ξ(q)| = H_{m'}(ψ)`. The real inequality then bounds
     `‖δ_P^{1/2}(m)‖ ‖χ(m)‖ = exp H_{m'}(ν)` by `exp(K₁ + s' log C₃) ‖x‖^{−s}`.
- *Decay input.* After unpacking the binders of `ParabolicCharacterDecayInput`, choose a closed
  representation on `Fin (N + 1)` by `exists_isClosedSubgroup_fin_succ` (using smoothness and
  connectedness from `IsConnectedReductive`) and apply the decay theorem with `hUpt` and
  `hU'pt` given by `rfl`. The monomorphism instances come from the closed-subgroup fields of
  the presentation: `r.data.i` is a split subtorus, and `r.data.f` is a monomorphism because
  its composite with `r.data.i` is the monomorphism `a ≫ l ≫ p` (`factor_comp`). The input
  supplies the remaining instance hypotheses.
- *Final reduction.* Combine the three inputs with
  `conditionalParabolicIntertwiningStatement_of_characterDecay`.
