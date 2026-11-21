# The differential of a smooth matrix representation preserves brackets

Module `Langlands.Geometry.Manifold.MatrixCoefficientLie` (namespace
`Langlands.Geometry.Manifold.MatrixCoefficientLie`). Internal supporting result for the adapted
Casimir element (Harish-Chandra, *Two theorems on semi-simple Lie groups*, 1966, proof of
Lemma 33), where the invariant form on the Lie algebra is a trace form of a faithful matrix
representation. It is the standard fact that the differential of a Lie group homomorphism into a
matrix group is a Lie algebra homomorphism, proved here by testing on smooth functions.

## Setting

`E` is a real normed space, `I : ModelWithCorners ℝ E H`, `G` a real Lie group
(`LieGroup I ∞ G`), `𝕜` a real normed algebra (`NormedRing`, `NormedAlgebra ℝ 𝕜`), `N` a finite
type with decidable equality, and `φ : G →* Matrix N N 𝕜` a monoid homomorphism whose entries
`g ↦ φ g a b` are `C^∞` (`ContMDiff I 𝓘(ℝ, 𝕜) ∞`). Derivatives of vector-valued functions are
Mathlib's `mvfderiv`.

## Declarations

- `mvfderiv_clm_comp`: for `Φ : M → F` differentiable at `x` and a continuous real-linear
  `L : F →L[ℝ] F'`, `mvfderiv (L ∘ Φ) x v = L (mvfderiv Φ x v)` (chain rule `mvfderiv_comp_apply`;
  a continuous linear map is its own derivative).
- `entryMap φ : M → (N → N → 𝕜)` (the entries of a matrix-valued map, as a map into a normed
  space), `entryDerivative I φ x v` (the matrix of entrywise derivatives), `contMDiff_entryMap`,
  `entryCLM a b` (the `(a, b)` entry as a continuous linear map) and `mvfderiv_entryMap`
  (`mvfderiv` of the entry map is the entrywise derivative).
- `testFunctional P Q ℓ i j`: the continuous real-linear functional
  `m ↦ (ℓ ((P * m * Q) i j) : ℂ)` on `N → N → 𝕜`, for matrices `P`, `Q` and
  `ℓ : 𝕜 →L[ℝ] ℝ`; `testFunctional_apply` expands it as a double sum.
- `mvfderiv_test` and `contMDiff_test`: the function `g ↦ (ℓ ((P * φ g * Q) i j) : ℂ)` is
  `C^∞`, and its derivative at `x` in direction `v` is
  `ℓ ((P * entryDerivative I φ x v * Q) i j)`.
- `matrixDifferential I φ : GroupLieAlgebra I G →ₗ[ℝ] Matrix N N 𝕜`, `X ↦` the entrywise
  derivative of `φ` at `1` in direction `X` (`matrixDifferential_apply`). Linearity holds because
  each `mvfderiv` at `1` is linear.
- `groupDirectionalValue_test`: with Library's right-orbit derivative
  `groupDirectionalValue I X f g = mvfderiv I (h ↦ f (g * h)) 1 X`, the test function `f_{P,Q}`
  is sent to `f_{P, D X * Q}`, where `D = matrixDifferential I φ`. Indeed
  `f_{P,Q} (g * h) = f_{P * φ g, Q} h` because `φ` is multiplicative, and `mvfderiv_test` applies.
- `matrixDifferential_lie` (main result): for a complete model space and boundaryless model,
  `D ⁅X, Y⁆ = D X * D Y - D Y * D X`.

## Proof of `matrixDifferential_lie`

Fix an entry `(i, j)`. Because continuous linear functionals separate points of `𝕜`
(`SeparatingDual.eq_iff_forall_dual_eq`), it suffices to compare `ℓ` of both sides for every
`ℓ : 𝕜 →L[ℝ] ℝ`. Apply the Library commutator law
`Langlands.Geometry.Manifold.groupDirectionalValue_commutator_of_vectorFieldCommutator`, with its
calculus premise supplied by `smoothVectorFieldCommutator_proof`, to the smooth function
`f = f_{1,1}` at `g = 1`:
`X_⁅X,Y⁆ f (1) = X_X (X_Y f) (1) - X_Y (X_X f) (1)`. By `groupDirectionalValue_test` (used twice for
each iterated derivative) and `φ 1 = 1`, the three terms are `ℓ ((D ⁅X, Y⁆) i j)`,
`ℓ ((D X * D Y) i j)` and `ℓ ((D Y * D X) i j)`, as complex numbers with zero imaginary part.
Taking real parts (`exact_mod_cast`) gives the identity for `ℓ`. The order `D X * D Y - D Y * D X`
is the one produced by Mathlib's bracket on `GroupLieAlgebra` (bracket of left-invariant vector
fields) with this right-orbit derivative.
