# Regularity of Shahidi's line for the upper two-block parabolic

Module `Langlands.Global.Factors.CuspidalPairLineRegularity` states and proves
`Langlands.Global.CuspidalPairEisenstein.CuspidalPairLineRegularityStatement.{u}`.

## The statement

Let `F : Type u` be a number field, `r t : ℕ`, `N = r + t + 2`, and `P` the scheme block
parabolic of type `(r + 1, t + 1)` in the scheme `GL_N`, with the Library's chosen split
component and root presentation `blockRootData F (blockShape r t)` (module
`Langlands.Global.AdelicBlockEisensteinRoots`). Let `λ₁ = lineParameter F r t`
(module `Langlands.Global.Factors.CuspidalPairSchemeSeries`). The statement says: for every real
`R` there is a real `σ` such that, for every `s : ℂ` with `σ < Re s`, the parameter `s • λ₁` is
`R`-regular in the sense of `ParabolicRootPresentation.IsRegularParameter`, that is,
`R < B(Re(s λ₁)|_A, α)` for every root `α` of the split component `A` in the unipotent radical
(`unipotentRoots`), where `B` is the Weyl-induced positive form of the presentation
(`weylInducedCharacterForm`). The theorem `cuspidalPairLineRegularity` proves it.

Together with `CuspidalPairSchemeComparisonStatement`, this puts the parameters of the
cuspidal-pair Eisenstein series with `Re s` large in the convergence and agreement regions of the
Library's group-scheme Eisenstein statements (for example `EisensteinAbsoluteConvergenceStatement`
and `EisensteinMeromorphicContinuationStatement`).

## Implemented proof

Write `A` for the split component, `a : A → M` for its inclusion in the block Levi `M`,
`l : M → P` for the Levi inclusion and `p : P → GL_N` for the parabolic.

1. **Block determinants on the Levi** (namespace
   `Langlands.Global.AdelicBlockEisensteinGeometry`).
   `characterRestrict_blockLeviInclusion_parabolicBlockCharacter`: the block determinant
   characters of `P` (`parabolicBlockCharacter`) restrict along `l` to the block determinant
   characters `blockDeterminantCharacter` of `M`. Both are the determinant of the same diagonal
   block on every test point.
2. **Pairings with diagonal cocharacters.** `gmEndEquiv_eq_of_points` identifies an endomorphism of
   `𝔾_m` that is the `m`-th power on all points. `latticePairing_restrict_blockDeterminantCharacter`
   computes the pairing of a restricted block determinant with a cocharacter `ν` of a commutative
   group scheme mapping to `M`, when `ν` followed by the inclusion of `M` in `GL_N` is the diagonal
   cocharacter `diagonalCocharacter e` and `e` takes the constant value `c` on the block: the
   pairing is `(size of the block) · c`. The proof evaluates on points
   (`pointsEquiv_diagonalCocharacter`) and takes the determinant of a diagonal submatrix.
3. **Two cocharacters of `A`.** `exists_diagonalCocharacter_lift` lifts the defining diagonal
   cocharacter `diagonalCocharacter (blockShapeWeight B)` of the block parabolic through `a`
   (`IsSplitComponent.exists_cocharacter_factor_of_dynamicCentralizer`, since its centralizer is
   the block Levi). `scalarLeviCocharacter` factors the scalar torus through the block Levi, and
   `exists_scalarTorus_lift` lifts it to `A` (`IsSplitComponent.exists_factor`; centrality in the
   Levi comes from `CoverPreimage.isCentral_of_comp_mono`).
4. **A spanning set.** `restrictedBlockDeterminant B i` is `1 ⊗ (det_i ∘ a)` in
   `Vstar A = ℝ ⊗ X^*(A)`. `mem_span_restrictedBlockDeterminant`: these span `Vstar A`. The
   restriction `X^*(M) → X^*(A)` has finite-index image
   (`IsSplitComponent.finiteIndex_range_characterRestrict`), so a multiple of every character of
   `A` is a restriction; the characters of `M` are integral combinations of the block
   determinants (`blockDetCombination_surjective`).
5. **The cuspidal-pair case** (namespace `Langlands.Global.CuspidalPairEisenstein`).
   `lineRestriction F r t` is `x = Re(λ₁)|_A` and `lineRestriction_eq` writes it as
   `((t+1)/N) X₁ - ((r+1)/N) X₂` in terms of the restricted block determinants. `scalarLift` and
   `diagonalLift` are the two lifts of step 3. Step 2 gives the pairings
   `⟨Xᵢ, scalarLift⟩ = size of block i` and `⟨Xᵢ, diagonalLift⟩ = -(i)·(size of block i)`
   (the weight of block `i` is `-i`, `blockShapeWeight_index`), hence
   `pair_lineRestriction_scalarLift : ⟨x, z⟩ = 0` and
   `pair_lineRestriction_diagonalLift : ⟨x, η⟩ = (r+1)(t+1)/N > 0`.
6. **The central line.** `lineRestriction_line`: every `y ∈ Vstar A` that vanishes on all
   cocharacters of `A` whose image in `GL_N` is central is a real multiple of `x`. By step 4,
   `y = c₁ X₁ + c₂ X₂`; vanishing on the scalar lift gives `(r+1) c₁ + (t+1) c₂ = 0`, so
   `y = (c₁ N/(t+1)) x`.
7. **Positivity on the unipotent roots.** `weylInducedCharacterForm_lineRestriction_pos`: for every
   `α ∈ unipotentRoots`, `0 < B(x, 1 ⊗ α)`. Write `α = f ≫ β` for a positive relative root `β` of
   the presentation torus. By `MaximalLeviConeComplementLine.exists_smul_eq_of_line` and step 6,
   `1 ⊗ α = c • x` for a real `c`. By `restrict_positive_eq_zero_or_mem`, `α` is a relative root
   of `A` with positive pairing against the defining cocharacter
   `splitComponentCocharacter`. That cocharacter and `diagonalLift` define the same dynamic
   parabolic (`parabolic_eq_splitComponentCocharacter`,
   `isRepresentedBy_parabolic_diagonalCocharacter`), so
   `RelativeRoot.nonnegative_rootSupport_of_parabolic_le` gives `0 ≤ ⟨α, η⟩ = c ⟨x, η⟩`. Since
   `⟨x, η⟩ > 0`, `c ≥ 0`, and `c ≠ 0` because `α` pairs positively with the defining
   cocharacter. Hence `B(x, 1 ⊗ α) = c B(x, x) > 0` (`weylInducedCharacterForm_pos`).
8. **Regularity.** `parameterRealPart_smul_lineParameter`: `Re(s λ₁) = (Re s) Re(λ₁)` because the
   coefficients of `λ₁` are real. The unipotent roots form a finite set, so
   `exists_isRegularParameter_lineParameter` takes `σ` above `R / B(x, 1 ⊗ α)` for all of them.

## Provenance

This is a derived property of the Library's presentation of the block parabolic. In the source
setting it is the statement that the line `s ↦ s · 2ρ_P/N` enters the convergence region of
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), II.1.5, pp. 85–86,
for `Re s` large: the parameter `2ρ_P/N` pairs positively with the coroot of the unique simple
root of `A_M` in `U_P` for the maximal parabolic `P` of type `(r + 1, t + 1)`. The regularity
condition `IsRegularParameter` is the Library's formulation of the condition
`⟨Re λ, α^∨⟩ ≫ 0` of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), §2.2, p. 191, through the Weyl-induced form. The proof above uses
only the structure of the Library's presentation and the explicit diagonal and scalar
cocharacters of `GL_N`; it does not identify the split component with the block-scalar torus.
