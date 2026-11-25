# The block rotations `r_p(θ)` in closed form

Module: `Langlands.Representation.Archimedean.RealBlockRotation`.

## Purpose and provenance

The Library defines the rotation `r_p(θ) = blockRotation N p θ` in the coordinates `p, p + 1` of
`GL_N(ℝ)` as the matrix exponential `exp(θ W)` of `W = rotationGenerator N p = E_{p+1,p} - E_{p,p+1}`
(module `Langlands.Representation.Archimedean.StandardModule`). The block Fourier coefficients
`blockFourierCoefficient N p k f g = ∫₀^{2π} f(r_p(θ) g) e^{-ikθ} dθ` that define the Fourier
conditions of `realStandardModule` are integrals over these rotations.

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealCharacterPairFiltrationStatement`, which computes with
these Fourier coefficients. It proves elementary facts about `r_p(θ)`: the closed form
`r_p(θ) = 1 + (cos θ - 1) P + sin θ W` with `P = E_{p,p} + E_{p+1,p+1}` (when `p + 1 < N`), the
group law, `2π`-periodicity, the matrix entries, `r_p(π) = s_p s_{p+1}`, conjugation by the sign
matrices `s_j = signReflection N j` (module `RealJacquetReduction`), and the commutation of
rotations in disjoint blocks. These are standard facts about plane rotations. The module makes
no literature assertion, so it has no literature sources. The definitions `ia`, `ib`,
`blockProj` and `rotMatrix` are internal notation for the proofs.

Notation: `E_{i,j}` is the matrix unit `Matrix.single i j 1`. All indices are the natural
numbers `p` and `p + 1` viewed in `Fin N`, which needs the hypothesis `h : p + 1 < N`.

## Declarations

### Notation

- `ia h : Fin N` is the index `p`, and `ib h : Fin N` is the index `p + 1`, for
  `h : p + 1 < N`. `ia_ne_ib h`: they are distinct.
- `blockProj h` is the matrix `P = E_{p,p} + E_{p+1,p+1}`, the projection onto the two
  coordinates of the block.
- `rotationGenerator_eq h`: `rotationGenerator N p = E_{p+1,p} - E_{p,p+1}`.
- `gen_mul_gen h`: `W * W = -P`. `gen_mul_proj h`: `W * P = W`. `proj_mul_gen h`: `P * W = W`.

### Closed form

- `rotMatrix h θ` is the matrix `1 + (cos θ - 1) • P + sin θ • W`.
- `hasDerivAt_rotMatrix h θ`: the derivative of `θ ↦ rotMatrix h θ` at `θ` is
  `W * rotMatrix h θ`. This follows from `W * P = W` and `W * W = -P`.
- `blockRotation_val_eq h θ`: the underlying matrix of `blockRotation N p θ` is
  `rotMatrix h θ`. Proof: the derivative of `t ↦ exp(t • (-W)) * rotMatrix h t` is
  `-W exp(-tW) M(t) + exp(-tW) W M(t) = 0`, so this function is constant, with value `1` at
  `t = 0`. Multiplying `exp(θ W) * (exp(-θ W) * rotMatrix h θ) = exp(θ W)` and using
  `exp(θW) exp(-θW) = 1` gives the claim.

### Group law and periodicity

- `blockRotation_add N p θ φ`: `r_p(θ + φ) = r_p(θ) r_p(φ)`, since `θW` and `φW` commute.
- `blockRotation_zero N p`: `r_p(0) = 1`.
- `blockRotation_neg N p θ`: `r_p(-θ) = r_p(θ)⁻¹`.
- `blockRotation_two_pi h`: `r_p(2π) = 1`, from the closed form with `cos 2π = 1` and
  `sin 2π = 0`.
- `blockRotation_add_two_pi h θ`: `r_p(θ + 2π) = r_p(θ)`.

### Entries

- `blockProj_apply h i j`: the entry `(i, j)` of `P` is `1` if `i = j` and `i ∈ {p, p+1}`, and
  `0` otherwise.
- `rotationGenerator_apply N p i j`: the entry `(i, j)` of `W` is `1` at `(p+1, p)`, `-1` at
  `(p, p+1)` and `0` elsewhere (this is the definition).
- `blockRotation_apply h θ i j`: the entries of `r_p(θ)` are `sin θ` at `(p+1, p)`, `-sin θ`
  at `(p, p+1)`, `cos θ` at `(p, p)` and `(p+1, p+1)`, `1` at the other diagonal positions, and
  `0` elsewhere.

### The rotation by `π` and the sign matrices

The sign matrix `s_j = signReflection N j` is the diagonal matrix with `-1` at position `j`
and `1` elsewhere, an element of `O(N)`. It is viewed in `GL_N(ℝ)` through `Unitary.toUnits`.

- `blockRotation_pi h`: `r_p(π) = s_p s_{p+1}`, the diagonal matrix with `-1` at `p` and
  `p + 1` and `1` elsewhere.
- `signReflection_mul_blockRotation_mul_of_mem h j hj θ`: if `j = p` or `j = p + 1`, then
  `s_j r_p(θ) s_j = r_p(-θ)`.
- `signReflection_mul_blockRotation_mul_of_not_mem h j hj θ`: if `j ≠ p` and `j ≠ p + 1`, then
  `s_j r_p(θ) s_j = r_p(θ)`.

These three are proved entry by entry from `blockRotation_apply`: conjugation by a diagonal
sign matrix multiplies the entry `(i, k)` by the signs at `i` and `k`, so it changes the sign of
the two off-diagonal entries `±sin θ` exactly when `j` is one of the two block coordinates.

### Disjoint blocks commute

- `rotationGenerator_mul_eq_zero hd`: if `p + 1 < p'` or `p' + 1 < p`, then the generators
  satisfy `W_p W_{p'} = 0`, because the columns used by `W_p` (`p`, `p + 1`) and the rows used
  by `W_{p'}` (`p'`, `p' + 1`) are disjoint.
- `blockRotation_commute hd θ φ`: under the same hypothesis,
  `r_p(θ) r_{p'}(φ) = r_{p'}(φ) r_p(θ)`. The generators commute (both products are zero), so
  `exp(θ W_p) exp(φ W_{p'}) = exp(θ W_p + φ W_{p'}) = exp(φ W_{p'}) exp(θ W_p)`.
