# Polynomial growth of real additive factors

This helper module shows that the matrices of the integer points of a one-dimensional
additive group inside a real group have polynomially bounded entries.

## Setting

`VectorGroup.groupScheme (CommRingCat.of ℝ) 1` is the additive group `𝔾ₐ` over `ℝ`, with
coordinate algebra `VectorGroup.coordinateAlgebra (CommRingCat.of ℝ) 1` (polynomials in one
variable). `VectorGroup.coordinateOnePoint ℝ` is its real point with coordinate `1`, so its
`N`-th power is the point with coordinate `N`.

## Declarations

- `RealAdditiveFactor.ΓSpecIso_appTop_vectorGroup`: pulling back a global function `P` of
  `𝔾ₐ` (a polynomial, transported by `Scheme.ΓSpecIso`) along a real point `x` gives
  `eval (coordinates of x) P`. The proof identifies `x` with an algebra homomorphism
  through `Corepresented.adjunction_homEquiv_symm_apply` and uses `MvPolynomial.aeval_unique`
  together with the uniqueness of ring homomorphisms `ℝ →+* ℝ`.
- `RealAdditiveFactor.ΓSpecIso_coordinates_pow`: the coordinate of
  `VectorGroup.coordinateOnePoint ℝ ^ N` is `N`.
- `RealAdditiveFactor.exists_rationalMatrix_entry_bound` (main result): for a group scheme
  `G` over `ℝ`, a matrix representation `ρ : MatrixRepresentation G n`, a homomorphism
  `φ : 𝔾ₐ ⟶ G`, and indices `i j`, there are `d : ℕ` and `c > 0` such that for every `N : ℕ`,
  `|ρ.rationalMatrix (rationalPoints.map φ (coordinateOnePoint ℝ ^ N)) i j| ≤ c (N + 1)^d`.

## Proof of the main result

The entry `(i, j)` of `ρ(φ(x))` is the pullback along `x` of the global function
`f = (φ ≫ ρ)^*(entry i j)` of `𝔾ₐ` (`MatrixRepresentation.rationalMatrix_apply_apply`). By
`ΓSpecIso_appTop_vectorGroup` its value at the point with coordinate `N` is `P(N)`, where
`P` is the polynomial of `f`. The Library's `Langlands.Plancherel.polynomial_evaluation_power_bound`
bounds `|P(N)|` by `c (N + 1)^d`.

## Provenance (internal)

An internal lemma for the compactness half of `RealAnisotropicCompactConnectedStatement`.
It is the real analogue of the Library's non-archimedean
`VectorGroup.exists_isCompact_powers_map_coordinateOne`, used in
`Langlands.GroupScheme.Rational.CommutingFactorizationIntegrality`.
