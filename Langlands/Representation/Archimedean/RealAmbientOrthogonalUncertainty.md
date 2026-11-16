# Adjacent-rotation uncertainty in arbitrary ambient rank

This is internal infrastructure for the real induction-block swap. It defines the
three-coordinate block embedding and proves an uncertainty theorem for adjacent
coordinate rotations of the orthogonal group in any ambient rank. It does not
construct a swap intertwiner or establish the full `RealInducedSwapStatement`.

For an ambient dimension `n` and a starting position `p` with `p + 3 ≤ n`, the
selected definition `RealOrthogonalBlock.block` is the monoid homomorphism
`GL₃(ℝ) → GLₙ(ℝ)` that places its argument in the coordinates `p,p+1,p+2` and
acts as the identity on the other coordinates. Its value matrix is
`P M Pᵀ + (1 - P Pᵀ)`, where `P` is the rectangular coordinate inclusion matrix.
The namespace used below is `Langlands.Archimedean.RealOrthogonalBlock`.

The construction follows the rectangular inclusion pattern of the published
`ComplexBlockRestriction` module, using three real coordinates in place of two
complex coordinates. Its algebraic verification is internal: `Pᵀ P = 1`, so the
linear block map preserves multiplication, commutes with transpose, and has
zero product with the complementary projection. These identities prove that
`block` is a monoid homomorphism, is injective, is continuous, and maps `O(3)`
into `O(n)`. The auxiliary entry lemmas describe both the block coordinates and
the identity outside them.

`restrictCoset p hp k` is the complex-linear map
`f ↦ (g ↦ f (block p hp g * k))`. It preserves continuity for any right coset
representative `k`. The theorem `restrictCoset_mem_kFiniteVectors` proves that it
preserves right orthogonal finiteness when `k ∈ O(n)`. If `u ∈ O(3)`, a right
translate of the restricted function by `u` is the restriction of the ambient
right translate by `k⁻¹ * block p hp u * k`. This conjugate belongs to `O(n)`.
Consequently the span of the restricted right translates lies in the image of
the finite-dimensional span of the ambient right translates. The theorem makes
no finiteness assertion for a noncompact coset representative.

`block_blockRotation` identifies the images of the rotations `r₀` and `r₁` of
`GL₃(ℝ)` with the rotations `rₚ` and `rₚ₊₁` of `GLₙ(ℝ)`. It follows from the
closed form `1 + (cos θ - 1) P + sin θ W` in `RealBlockRotation`: both the
coordinate projection and rotation generator transfer through the linear block
map. Substitution in the integral gives
`blockFourierCoefficient_restrictCoset`: the Fourier coefficient of a restricted
function along `r_q` equals the ambient coefficient along `r_(p+q)`, evaluated
at the corresponding embedded point times `k`, for `q + 1 < 3`.

The theorem `adjacent_uncertainty` has the following precise scope. Suppose
`(r,s)` is either `(0,1)` or `(1,0)`, and the natural cutoffs satisfy `m' < m`.
Let `f : GLₙ(ℝ) → ℂ` be continuous and right `O(n)`-finite. Suppose that at every
point of `O(n)` its Fourier coefficients along `r_(p+r)` vanish for `|j| < m`,
and its coefficients along `r_(p+s)` vanish for `m' ≤ |j|`. Then `f` vanishes on
`O(n)`. The bound `p + 3 ≤ n` is retained as an explicit input.

For each `k ∈ O(n)`, the implemented proof applies the published theorem
`RealOrthogonalUncertainty.realOrthogonalBlockUncertainty` to
`restrictCoset p hp k f`. Continuity and right finiteness follow from the
restriction lemmas. The Fourier identities transfer the two vanishing
hypotheses, since `block g * k` is compact whenever `g ∈ O(3)`. Evaluation at the
identity of `O(3)` gives `f k = 0`. The conclusion concerns the compact group;
vanishing on all of `GLₙ(ℝ)` would require additional hypotheses and an argument.

All content is derived from the published rank-three uncertainty theorem,
rotation formulas, and the definitions of right finiteness and Fourier
coefficients. No external literature assertion or unproved swap premise is
introduced.
