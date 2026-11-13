# Product-formula lower bounds for diagonal adelic heights

Module `Langlands.Global.AdelicSiegelDiagonalHeightBound`, namespace
`Langlands.Global.AdelicSiegelFactors`.

Author: Worker 5644.

## Role and provenance

This module is Part A of the planned proof of
`Langlands.Global.AdelicSiegelFactors.SiegelNormMinimalityStatement` (Mœglin–Waldspurger,
*Spectral decomposition and Eisenstein series*, 1995, I.2.2 (vii), printed pp. 20–21; source id
`moeglin-waldspurger-1995-spectral-decomposition`), as divided in the context of Task 5910.
Mœglin–Waldspurger's argument that `‖γ g‖ ≫ ‖g‖` on a Siegel set rests on the following
idea: a rational matrix cannot make a diagonal matrix of positive real ideles smaller,
because of the product formula. This module proves that idea for the full adelic height
`AdelicMatrixHeight.height`. It then transfers the inequality to the image of the
positive-real points of a split torus under any group-scheme homomorphism. All results here
are internal auxiliary lemmas; none is a published statement.

Notation: `H = AdelicMatrixHeight.height F N` on `AdelicGL F N`, and
`d = ∑_{v ∞} mult v = [F : ℚ]`.

## Results

### Product formula for actual adele projections

- `norm_infiniteProjection_diagonal`, `norm_finiteProjection_diagonal`: for `x : F`, the
  local norm of the projection of the diagonal adele `diagonal F x` at an infinite place `v`
  is `v x`. At a finite place it is the Mathlib finite-place absolute value, transported
  along `NumberField.FinitePlace.equivHeightOneSpectrum`.
- `hasFiniteMulSupport_norm_finiteProjection_diagonal`: for `x ≠ 0` these finite local norms
  are `1` at all but finitely many places.
- `prod_norm_diagonal_eq_one`: for `x ≠ 0`,
  `(∏_{v ∞} ‖x‖_v ^ mult v) · ∏ᶠ_{v finite} ‖x‖_v = 1`. This is Mathlib's
  `NumberField.prod_abs_eq_one`, rewritten through the two norm lemmas and
  `finprod_comp_equiv`.

### Entry lower bound and diagonal upper bound

- `pow_le_height_of_entry`: let `g ∈ GL_N(𝔸_F)` have an entry `g i j = ρ · s` with
  `ρ ∈ F^×` and `s` the positive scalar idele `PositiveRealIdeles.full F s`, equal to the
  positive real `s` at every infinite place and `1` at every finite place. Then
  `(N · s)^d ≤ H(g)`. Proof: the local maxima of `g` dominate the entry. They are at least
  `|ρ|_v · s` at infinite places and `‖ρ‖_v` at finite places. Multiply the product formula
  for `ρ` by `(N s)^d` and compare factor by factor (`Finset.prod_le_prod₀`,
  `finprod_le_finprod₀`).
- `exists_inv_entry_ne_zero_and_entry_ne_zero`: for `R ∈ GL_N(F)` and each index `j` there is
  a `k` with `(R⁻¹) j k ≠ 0` and `R k j ≠ 0`. Otherwise the `(j, j)` entry of `R⁻¹ R = 1`
  would be `0`.
- `inv_diagonalMatrix`, `localMaximum_diagonalMatrix_le`: the inverse of a diagonal unit
  matrix is diagonal with the inverse entries. A local maximum of a diagonal unit matrix is
  bounded by any common bound on the norms of its entries and their inverses.
- `height_diagonalMatrix_full_le`: let `D = diag(full(r_1), …, full(r_N))` with
  `r_j ∈ ℝ_{>0}`, and let `M` bound every `r_j` and every `r_j⁻¹`. Then
  `H(D) ≤ (N · M)^d`: every finite local maximum of `D` equals `1`, and every infinite one
  is at most `M`.

### Diagonal inequality

- `height_diagonalMatrix_full_le_height_rational_mul`: for `R ∈ GL_N(F)` and `D` as above,
  `H(D) ≤ H(R_𝔸 · D)`, where `R_𝔸` is the diagonal image of `R`. Proof: choose `j₀`
  maximizing `φ_j = max(r_j, r_j⁻¹)`, so `H(D) ≤ (N φ_{j₀})^d`. Take `k` from the previous
  lemma.
  - If `φ_{j₀} = r_{j₀}`: the entry `(R_𝔸 D) k j₀ = R k j₀ · full(r_{j₀})` has a nonzero
    rational factor, so `pow_le_height_of_entry` gives `(N r_{j₀})^d ≤ H(R_𝔸 D)`.
  - If `φ_{j₀} = r_{j₀}⁻¹`: use `H(R_𝔸 D) = H((R_𝔸 D)⁻¹)` (`height_inv`). The entry
    `(D⁻¹ R_𝔸⁻¹) j₀ k = R⁻¹ j₀ k · full(r_{j₀}⁻¹)` gives `(N r_{j₀}⁻¹)^d ≤ H(R_𝔸 D)`.

  The constant is `1`. This is sharper than the bound `N^d` that Task 5910's route sketch
  allows.

### Transfer to split tori

- `adelicMatrix_map_eq_matrixAt`: for `f : T → G` and a splitting `e : T ≅ 𝔾_m^I`, the
  representation matrix of `map f y` is `matrixAt I (rho.restrict (e.inv ≫ f))` at the
  coordinates of `y`.
- `adelicMatrix_rational`: the representation matrix of the principal adelic point
  `rational F G q` is the diagonal image of the rational matrix
  `rho.affineMatrix (CommAlgCat.of F F) q`. This is `affineMatrix_naturality` for the algebra
  map `F → 𝔸_F`.
- `exists_adelicHeight_map_le_rational_mul` (the Part A interface fixed in Task 5910's
  context): let `T₀` be a split torus and `f : T₀ → G` a homomorphism. Then there is `c ≥ 0`
  such that for every intrinsic positive point `a` of `T₀` and every rational point `q`,
  `adelicHeight(map f a) ≤ c · adelicHeight(rational q · map f a)`.

  Proof. Choose a splitting `e` of `T₀`. By `exists_diagonalizingMatrix`, applied to
  `rho.restrict (e.inv ≫ f)`, there are `B ∈ GL_N(F)` and integer weight vectors `w_j` that
  diagonalize the restricted representation over every `F`-algebra. Let `B_𝔸` be the image of
  `B`, and put `c = (H(B_𝔸) H(B_𝔸⁻¹))²`.

  The point `a` lies in the coordinate positive subgroup (`subgroup_eq_intrinsicSubgroup`),
  so `a = full(x)` for some `x : I → ℝ_{>0}`. Hence
  `adelicMatrix(map f a) = B_𝔸 D B_𝔸⁻¹` with `D = diag(full(r_j))` and
  `r_j = ∏_k x_k^{w_j k}`. Write `Q` for the rational matrix of `q`, `Q_𝔸` for its image, and
  `X = Q_𝔸 B_𝔸 D B_𝔸⁻¹` for the matrix of `rational q · map f a`. Apply the diagonal
  inequality to `R = B⁻¹ Q B`, and use `B_𝔸⁻¹ Q_𝔸 B_𝔸 D = B_𝔸⁻¹ X B_𝔸`. Then
  `height_mul_le` gives
  `H(B_𝔸 D B_𝔸⁻¹) ≤ H(B_𝔸) H(D) H(B_𝔸⁻¹) ≤ H(B_𝔸) H(B_𝔸⁻¹) H(X) H(B_𝔸) H(B_𝔸⁻¹) = c · H(X)`.

The final theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
A Lake build of this module with the three others of the proof over Library commit
`f2b3d7dcdd52af1923cd0bf5c4d90beda3118720` reports no errors or warnings (diagnostic
`12ca220b-423d-4a37-b422-3120df9ecce6`).
