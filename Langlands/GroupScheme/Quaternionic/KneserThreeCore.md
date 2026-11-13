# The exterior-square map `SU₄ → U₃` over a presented quaternion-type ring

Module `Langlands.GroupScheme.Quaternionic.KneserThreeCore`, namespace
`Langlands.GroupScheme.KneserThree.Presentation`. Internal algebra for the `A₃ = D₃` comparison
used in the proof of `KneserThreeSpinSubgroupStatement`. There is no characteristic assumption.
Throughout, `P : Presentation A B` (module `KneserThreePresentation`) writes `B = ι(A) ⊕ j ι(A)`
with `j² = δ`, and `ā` is the involution of `A`.

## Mathematical content

On `A⁴` with basis `(top, m₀, m₁, bot) = (e₀, e₁, e₂, e₃)` take the Hermitian Gram matrix `gram`:
`1` at `(top, bot)` and `(bot, top)`, `diag(1, -δ)` on `m₀, m₁`. For `g` special unitary for
`gram`, the exterior square `X = Λ² g` (module `ExteriorSquareMatrix`) on `A⁶` commutes with the
semilinear map `ξ ↦ Jm ξ̄`, where `Jm = pfaffian · (Λ² gram)ᵀ`. This map squares to `δ`, so it makes
`A⁶` a right `B`-module, free of rank three with basis
`B₁ = e₀∧e₁`, `B₂ = (θ e₃∧e₁) ℓ`, `B₃ = e₀∧e₃`, where `θ̄ = -θ` and `ℓ = ι l₁ + j ι l₂`.
`cmap g` is the matrix over `B` of the `B`-linear map `X` in this basis.

## Definitions

* `gram`, `conjT M = (M.map conj)ᵀ`, and `IsSpecialUnitary g`:
  `conjT g * gram * g = gram ∧ det g = 1`.
* `structureMatrix = pfaffian * (ExteriorSquare.matrix gram)ᵀ`; `structureMatrix_eq` gives it in
  coordinates (`e₀∧e₁ ↦ e₀∧e₂ ↦ δ e₀∧e₁`, `e₁∧e₃ ↦ -e₂∧e₃`, `e₂∧e₃ ↦ -δ e₁∧e₃`,
  `e₀∧e₃ ↦ -e₁∧e₂`, `e₁∧e₂ ↦ -δ e₀∧e₃`).
* `frame θ l₁ l₂ : Matrix (Fin 6) (Fin 3 × Fin 2) A`: columns are the standard coordinates of
  `B₁, B₁ j, B₂, B₂ j, B₃, B₃ j`. `frameInv l₁ l₂ w` is its inverse when
  `w · θ · (l₁ l̄₁ - δ l₂ l̄₂) = 1` (`frame_mul_frameInv`, `frameInv_mul_frame`).
* `standardStructure`: on `A^{3×2}`, `e_{i,0} ↦ e_{i,1}`, `e_{i,1} ↦ δ e_{i,0}`.
* `adapted θ l₁ l₂ w g = frameInv * Λ² g * frame`.
* **`cmap θ l₁ l₂ w g : Matrix (Fin 3) (Fin 3) B`**, with `(i, k)` entry
  `elem (adapted g (i,0) (k,0)) (adapted g (i,1) (k,0))`.
* `kappa θ l₁ l₂ = θ (l₁² + δ l̄₂ l₂)` and
  `skewHermitian θ l₁ l₂ = [[0, ℓ, 0], [ℓ, 0, 0], [0, 0, -κ]]` (`-κ` is `elem (-κ) 0`);
  `skewHermitianSymplectic` is `block skewHermitian * blockSymplectic` in coordinates. Under `hθ`
  and `hl` (below) one has `bar ℓ = -ℓ` and `κ̄ = -κ`, so this matrix is skew-Hermitian for
  `Presentation.bar`, not Hermitian (`conjTranspose_skewHermitian`). It corresponds to a Hermitian
  matrix only for a different, twisted involution, which this module does not use.
* `binary θ θinv g b`: the `4 × 4` matrix with `g` on `top, bot` twisted by `diag(1, θ)`
  (entries `g₀₀, g₀₁ θinv, θ g₁₀, g₁₁`) and `rep b` on `m₀, m₁`. `product g b` is
  `[[g₀₀ b, g₀₁ b, 0], [g₁₀ b, g₁₁ b, 0], [0, 0, 1]]`; `twist l₁ l₂ = diag(1, ℓ, 1)`, and
  `twistInv linv = diag(1, linv, 1)`.

## Results

Hypotheses as needed: `hθ : θ̄ = -θ`, `hl : l̄₁ = -l₁`, `hw : w θ (l₁ l̄₁ - δ l₂ l̄₂) = 1`.

* `IsSpecialUnitary.mul`, `isSpecialUnitary_one`.
* `matrix_mul_structureMatrix`: for special unitary `g`, `Λ² g * Jm = Jm * conj(Λ² g)`. Proof: with
  `X = Λ² g`, `Γ = Λ² gram`, unitarity gives `Xᵀ Γᵀ X̄ = Γᵀ` and `det g = 1` gives
  `X B Xᵀ = B`; so `X B Γᵀ = X B (Xᵀ Γᵀ X̄) = B Γᵀ X̄`.
* `frame_mul_standardStructure`: `frame * standardStructure = Jm * conj(frame)` (uses `hθ`); hence
  `frameInv_mul_structureMatrix`, and `adapted_mul_standardStructure`: for special unitary `g`,
  `adapted g` commutes with `standardStructure` up to `conj`.
* `block_cmap`: for special unitary `g`, `block (cmap g) = adapted g` (the commutation says that
  `adapted g` consists of `rep` blocks).
* `adapted_mul`, `adapted_one`; **`cmap_mul`**: `cmap (g g') = cmap g * cmap g'` for special
  unitary `g, g'`, and `cmap_one`. Proof: `block` is injective and multiplicative.
* `conjTranspose_skewHermitian`: under `hθ` and `hl`,
  `conjTranspose skewHermitian = -skewHermitian`. Proof: entrywise, `bar (elem l₁ l₂) =
  elem (-l₁) (-l₂)` and `bar (elem (-κ) 0) = elem κ 0`.
* `block_skewHermitian_mul_blockSymplectic`,
  `frame_mul_skewHermitianSymplectic_mul_transpose`:
  `frame * skewHermitianSymplectic * frameᵀ = κ • pfaffian`.
* **`cmap_mul_skewHermitian_mul_conjTranspose`**: for special unitary `g`,
  `cmap g * skewHermitian * conjTranspose (cmap g) = skewHermitian`. Proof: apply `block`; with
  `N = adapted g` and `M = block skewHermitian * blockSymplectic`, `block (conjTranspose (cmap g)) =
  -(S Nᵀ S)` (`S = blockSymplectic`, `S² = -1`), and `N M Nᵀ = M` follows from
  `frame M frameᵀ = κ pfaffian` and `X pfaffian Xᵀ = pfaffian`.
* `cmap_eq_of_adapted_eq_block`: if `adapted g = block Z` then `cmap g = Z`.
* `frame_eq_mul_block_twist`: `frame θ l₁ l₂ = frame θ 1 0 * block (twist l₁ l₂)`.
* `matrix_binary_mul_frame`: for `θ θinv = 1`, `g` with entries fixed by the involution and
  `det g = 1`, and `b` with `fst b · conj(fst b) - δ snd b · conj(snd b) = 1`:
  `Λ² (binary θ θinv g b) * frame θ 1 0 = frame θ 1 0 * block (product g b)`.
* **`cmap_binary`**: under the same hypotheses, `hw`, and `ℓ · linv = 1`:
  `cmap (binary θ θinv g b) = twistInv linv * product g b * twist l₁ l₂`.

The numerical identities among explicit matrices are proved by expanding entries and `ring` or
`linear_combination`; the structural statements are matrix algebra.
