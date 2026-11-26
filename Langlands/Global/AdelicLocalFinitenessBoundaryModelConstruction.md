# Construction of the compact boundary model

Module `Langlands.Global.AdelicLocalFinitenessBoundaryModelConstruction`. Setting of
`AdelicLocalFinitenessLeftOperators`: a standard parabolic family `𝓕`, an Iwasawa subgroup `K` of
the standard minimal parabolic `P₀`, chamber coordinates `e` with `r` central coordinates, rates
`ra`, `rb` and thresholds `τ`.

## Coefficients

- `LocalFinitenessData.mdifferentiableOn_dirCoeff`: for admissible data `X` every coefficient
  `s ↦ X.dirCoeff J s ε k q` (module `AdelicLocalFinitenessSolutionComponents`) is complex
  differentiable on `W`. For a root direction it is a coefficient of `D_β(s)`; for a central
  direction it is a coefficient of `D̃_j(s)` (positive orientation) or a quotient of two
  coefficients of `D̃_j(s)` by its non-vanishing constant coefficient (negative orientation).

## The right-hand family

- `boundaryRhsCore … Tbox ω`: the operator `Tbox P ε : V → L²(siegelHaar|box)` on a box
  coordinate `ω = (P, ε, none)`, and `0` on a direction `ω = (P, ε, some k)`.
- `boundaryRhs … Tbox D s`: the assembly (`piAssemble`) over all coordinates of
  `boundaryRhsCore … ω ∘ D s`, for a family `D s : B → V`; it has the codomain of `boundaryLhs`.
- `isCompactOperator_boundaryRhs`: if every `Tbox P ε` is compact, so is every `boundaryRhs … s`.
- `isHolomorphicOperatorFamilyOn_boundaryRhs`: if `s ↦ D s` is weakly holomorphic on `S`, so is
  `s ↦ boundaryRhs … s`.

## The boundary model

`exists_boundaryModel` assumes `PositiveTorusSplitComponentStatement`, local-finiteness group data
`(u, t, z)` for `𝓕`, a Siegel algebraic setup `j : T₀ → T`, an equivalence `d_T` of real duals equal
to `realCharacterDualMap` of `T → P₀`, chamber coordinates `e` with `(e (d_T h))_α = h_α / step_α`
(`step_α > 0`), whose vanishing central part forces the image in the real dual of `G` to vanish,
and which send the logarithms in `P₀` of `t_α` and `z_j` to the unit vectors; the rational
characters of `P₀` free of finite rank; and, for every `x ∈ G(𝔸)`, a rational translate `q x`
with finite part in a compact `Ω`, root coordinates `(e(H₀(q x)))_α ≥ θ_α` and
`ht(q x) ≤ M ht(x)^{t'}`. For admissible data `X`, an open compact level `L` and `s₀ ∈ W` it gives
an index `i₀` with `c_{i₀}(s₀) ≠ 0`, Hilbert spaces `B`, `C` and a `BoundaryModel` of `X` for
`i₀` at `s₀` (for the points `a_α = i(t_α)`, `z_j = i(z_j)`).

Construction, in this order:

1. `i(t_α)` and `i(z_j)` shift the chamber coordinates by unit vectors
   (`isCoordinateShift_torus`) and are Levi-normalizing (`isLeviNormalizingPoint_of_groupData`).
2. Coefficients: degrees `m P ε = dirDegree J_P` and coefficients `p s P ε = dirCoeff J_P s ε`
   for `P ⊆ Δ` (zero otherwise). `S` is the set of `s` with `c_{i₀}(s) ≠ 0` and total coefficient
   size `∑ ‖p s P ε k q‖` below its value at `s₀` plus one; it is open and contains `s₀`, and
   every coefficient bound on `S` is at most `M_c` (that value plus one).
3. Kernels: the level averages over `L` of the kernels `h_{i₀,k}` with respect to a common open
   level (`exists_common_level`), test functions left invariant under `L`.
4. The margin `δ` of `exists_smoothingOperators` for these kernels and the threshold
   `τ_α = θ_α − δ − 1`.
5. Rate thresholds for `τ` and `M_c` from `exists_residualOperators`, `exists_chamberEmbedding` and
   `exists_boxBoundaryOperator` (once for Hilbert spaces in the universe of `G`, once for `ℂ`), and
   the constant rates `ra = rb = ρ₀` at their maximum.
6. The polynomial bound of the weight (`adelicLocalFinitenessChamberWeight`), the growth exponent
   `R₀` and the smoothing operators `K_k : B → 𝔉^{R₀}_L` of `exists_smoothingOperators`, where `B`
   is `siegelHilbert hK e ra τ rb`.
7. `lhs s = boundaryLhs … E Lsh m p s` with the operators of `exists_residualOperators`; it is
   weakly holomorphic on `S` and an embedding at `s₀` by the strict bound.
8. `D s = (normalizedCoefficient i₀ k s • id)_k : B → ℓ²(B^{m_{i₀}})`, the compact operators
   `Tbox P ε` of `exists_boxBoundaryOperator` for `smooth = ∑_k K_k ∘ proj_k`, and
   `rhs s = boundaryRhs … Tbox D s`; `smooth (D s x) = (∑_k normalizedCoefficient i₀ k s • K_k) x`,
   which gives compatibility at `s₀` (if it vanishes, then `Tbox P ε (D s₀ x) = Tbox P ε 0`).
9. Lift of a solution `f` of `Ξ_main(s)` in `𝔉^R_L` (`s ∈ S`, `R ≥ R₀`), with function `φ`:
   - `φ` is continuous, left `G(F)`-invariant and right `L`-invariant; its Harish-Chandra
     components `φ_P` are the alternating sums of folded constant terms; they are measurable and
     invariant under `P₀(F) U_J(𝔸)` for `J = J_P`, and `∑_P φ_P = φ` (`sum_hcComponent`).
   - On every box, `φ_P` is square integrable (the operator of `exists_boxBoundaryOperator` for
     `E = ℂ`, `c ↦ c f`); every residual function vanishes (`residualFun_hcComponent_eq_zero`).
     Hence `φ` is square integrable for the Siegel weight (`exists_chamberEmbedding`).
   - `φ` descends to a measurable function on `G(F) \ G(𝔸)`, square integrable for the weighted
     automorphic measure since the quotient map is measure preserving from the Siegel measure;
     `x ∈ B` is its class, and the embedding of `x` is `φ` almost everywhere.
   - By the solution equation, the reproducing identity of the level averages
     (`sum_rightConvolution_levelAverage`) and `K_k x = δ(h'_k) φ`, the smoothed vector
     `(∑_k normalizedCoefficient i₀ k s • K_k) x` has function `φ`. This is the reproducing
     identity of the model, and on each box both `lhs s x` and `rhs s x` are `φ_P` almost
     everywhere; on each direction `lhs s x` is the vanishing residual function and `rhs s x = 0`.

The proof uses `maxHeartbeats 1600000`.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), 187–234, proof of Theorem 7.2, §7.6, pp. 219–220 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`): the operator `μ_s` is a strict
embedding, `ν_s` (the restrictions to the sets `S_P^B` of the components of the smoothed vector) is
compact, and the solutions of `Ξ_main(s)` lie in the weighted Siegel space; §7.7, pp. 220–221: the
orthants and the central equations. The level averaging of the kernels and the descent through
`G(F) \ G(𝔸)` are the adaptations to the Library's growth spaces `𝔉^R_L` and weighted Hilbert
spaces.
