# Schwartz domination of the leading rectangle in the real gap recurrence

This module is the real counterpart of the Library's `ComplexGapLeadingSchwartz`. Real matrices carry
the operator (row-sum) norm `Matrix.Norms.Operator`, as in `RealGapLeadingFourier`; `H` is the real
matrix height `realMatrixHeight`.

`leadingStack A Y` stacks a `k × k` matrix `A` above a `d × k` matrix `Y`. `norm_entry_le_opNorm` bounds
an entry by the operator norm.

`RealGapLeadingSchwartzStatement` (proved by `realGapLeadingSchwartz`): for `0 < k + d`, a Schwartz
function `Φ` on `(k + d) × k` real matrices and decay orders `p`, `q`, there is `C ≥ 0` with

`‖Φ(g · leadingStack A Y)‖ ≤ C · H(g)^{p+q} / ((1 + ‖A‖)^p (1 + ‖Y‖)^q)`

for all `g ∈ GL_{k+d}(ℝ)`. Multiplying by `g^{-1}` recovers the stack; the entries of `g^{-1}` are bounded
by `H(g)` (`norm_entry_le_realMatrixHeight`, `realMatrixHeight_inv`), so
`‖leadingStack A Y‖ ≤ (k + d) H(g) ‖g · leadingStack A Y‖`; each block has norm at most that of the stack;
and the Schwartz seminorm estimate of order `p + q` concludes.

`matrixDecay p X = (1 + ‖X‖)^{-p}` and `weightedMatrixTail M p s g = H(g)^M |det g|^s matrixDecay p g`.
`exists_integrable_weightedMatrixTail`: for every Haar measure `μ` on `GL_{r+1}(ℝ)` and every real `s`
with `(r + 1) + 2M ≤ s`, some `p` makes `weightedMatrixTail M p s` integrable for `μ`. The proof writes
`|det g|^s = (|det g|²)^M |det g|^τ |det g|^{r+1}` with `τ = s - (r + 1) - 2M`. The Library's bound
`realMatrixHeight_mul_absDet_sq_bound` controls `H(g) |det g|²` by a power of `1 + ‖g‖`, the Leibniz-formula bound
`|det g| ≤ (r + 1)! (1 + ‖g‖)^{r+1}` (`Langlands.Global.norm_det_le_factorial_mul_pow`) controls `|det g|^τ`, and `|det g|^{r+1}` cancels the density of Haar measure
with respect to matrix Lebesgue measure (`RealGodement.exists_realMatrixHaar_eq_smul` and
`integrable_forwardWeight_iff_of_eq_smul`); a large decay order then leaves an integrable power of
`1 + ‖g‖` for Lebesgue measure.

The complex module requires `(r + 1) + M ≤ s` for the normalized absolute value `|det g|_ℂ = |det g|²`
and uses the explicit complex Haar measure; the real threshold `(r + 1) + 2M` comes from the factor
`|det g|²` in the real height bound.
