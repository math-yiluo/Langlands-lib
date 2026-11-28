# Shell sums as Jacquet functions of degree pieces

Module `Langlands.Representation.Shahidi.OpenCellShellSum`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `determinantNorm_eq_zpow`: `|det m| = q^(-detExponent m)`; `detExponent_mul_of_determinantNorm`;
  `detExponent_torus_mul_unipotent_mul_torus`; `degreeΦ` (the Levi function `detExponent m₁`) and
  `liftDegree_law`; `liftDegree_lower`, `liftDegree_open`: the first-block degree at `lower(Y)`
  and at `w u'(Y)` is `openCellDepth Y`.
- `intertwiningJacquetKernel_eq_conj`: the kernel is `conj ψ(Y_(t,0))`, of norm `1`, and (for `ψ`
  of conductor `𝒪`, `intertwiningJacquetKernel_add_integral`) invariant under integral
  translations; `jacquetIntegrandAt_one`: for a Levi-invariant `Φ` the Jacquet integrand at `1`
  is `conj ψ(Y_(t,0)) F(lower Y)`.
- `shellSet`, `shellFinset hϖ e`: the classes of depth `e` (finite).
- `hasSum_jacquetFunction_degreePiece_one`: for `ψ` of conductor `𝒪` (additive conductor `0`) and
  a Levi-invariant `Φ`, the Jacquet integrand at `1` of the degree-`e` piece is integrable and
  `J[Φ_e](1) = ∑_(y ∈ shellFinset e) conj ψ(y_(t,0)) F(lower y)` (the integrand is then
  lattice-periodic and supported on finitely many classes, each of measure `1`).
- `jacquetFunction_degreePiece_one_of_neg`: under the same hypotheses it vanishes for `e < 0`;
  `hasSum_jacquetFunction_degreePiece_one_of_hasSum`: under the same conductor hypothesis, if
  `∑ w_i Φ_i = Φ` pointwise with every `Φ_i` and `Φ` Levi-invariant, then
  `∑ w_i J[(Φ_i)_e](1) = J[Φ_e](1)` (a finite sum of pointwise sums).
- `hasSum_shell_jacquetFunction`, `shellIdentity_iff`: for `ψ` of conductor `𝒪` and a function `f`
  with the target transformation law (`IsOpenCellSection`), the depth-`D` open-cell summands sum
  to `J[(fullΦ a c s)_D](1)`, so `ShellIdentity` is equivalent to
  `J[(fullΦ a c s)_D](1) = shellCoefficient (pairParameter q a c s) D` for all `D`.
- Integrability of the Jacquet integrand of a degree piece of a Levi-invariant `Φ` (no
  conductor hypothesis):
  - at `1` it is supported on the classes of depth `e` (`jacquetIntegrandAt_degreePiece_one`);
  - `integrable_jacquetIntegrandAt_degreePiece_torus`: write a torus point `ϖ^μ` as the block
    exchange of `diag(ϖ^μ₂, ϖ^μ₁)`, where `μ₂` is the first `t + 1` and `μ₁` the last `r + 1`
    coordinates of `μ`; after the change of variables `Y ↦ h₂⁻¹ Y h₁` of the rectangular
    conjugation (`h₁ = ϖ^μ₁`, `h₂ = ϖ^μ₂`), the translated amplitude of the degree-`e` piece
    vanishes off the classes of depth `e - ∑ μ₁` (`translatedLower_degreePiece_eq_zero`), so it is
    lattice-periodic with finite support on classes and the integrand is integrable;
  - `integrable_jacquetIntegrandAt_degreePiece`: at a general point `g`, if moreover `Φ` is
    Levi-equivariant for the standard characters of the two blocks, the Iwasawa decomposition
    `g = u ϖ^μ k` and the transport of integrability under the unipotent factor reduce to the
    torus case.

## Provenance

Derived from `Langlands.Representation.Shahidi.OpenCellHaar` and
`Langlands.Representation.Shahidi.OpenCellPieces`.
