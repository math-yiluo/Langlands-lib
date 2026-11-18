# Matrix polynomials vanishing on a finite-index subgroup of rational points

This helper module shows that, for a connected reductive group over an infinite field, a
polynomial identity in the matrix entries of a representation that holds on a finite-index
subgroup of the rational points holds on all rational points.

## Setting

`k` is a field, `G : GroupScheme (Spec (CommRingCat.of k))`, and
`ρ : MatrixRepresentation G n` with `n` a finite type. Rational points are
`G.affinePoints (CommAlgCat.of k k)`, and `ρ.affineMatrix (CommAlgCat.of k k)` sends a
rational point to its matrix in `GL n k`. Polynomials are in
`MvPolynomial (Coordinate n) k` (matrix entries and inverse entries) and are evaluated at a
matrix through `values`, as in `Langlands.Group.CompactMatrixZariskiClosure`.

## Declarations

- `MatrixRepresentation.matrixFunction ρ : MvPolynomial (Coordinate n) k →ₐ[k] Γ(G.X.left, ⊤)`
  substitutes the entries and inverse entries of the universal matrix
  `pointsEquiv n _ G.X ρ.hom.hom` into a polynomial. It is the global function
  `g ↦ p(ρ(g))` on `G`.
- `MatrixRepresentation.values_map`: `values` commutes with applying a ring homomorphism to
  the entries.
- `MatrixRepresentation.appTop_matrixFunction`: pulling `matrixFunction p` back along a
  rational point `x` gives the value `p(ρ(x))` (transported by `Dynamic.affineTestEquiv`).
  The proof uses `aeval_values_pointsEquiv` and `pointMatrix_eq_affineMatrix`.
- `MatrixRepresentation.eval_eq_zero_of_finiteIndex` (main result): assume `k` is infinite,
  `IsConnectedReductive G`, `H` is a subgroup of finite index of the rational points, and
  `p(ρ(h)) = 0` for every `h ∈ H`. Then `p(ρ(g)) = 0` for every rational point `g`.

## Proof of the main result

Choose representatives `g_q` of the cosets `q ∈ G(k)/H` and put
`F = ∏_q p(ρ(g_q)⁻¹ · _)`, built with `leftTranslate`. Every rational point `y` lies in some
coset `g_q H`, and the factor for that coset vanishes at `y`. So `matrixFunction F` vanishes
at every rational point. The rational points of a connected reductive group over an infinite
field are dense (`reductiveRationalPointDensity`), so they detect global functions
(`RationalDensity.rationalPointsDetectFunctions_of_dense`), and `matrixFunction F = 0`. The
scheme `G.X.left` is integral (`CharacterLatticeProof.isIntegral_of_smooth`, using
smoothness and connectedness), so its ring of global functions is a domain and one factor
`matrixFunction (p(ρ(g_q)⁻¹ · _))` is zero. Evaluating that factor at `g_q g` gives
`p(ρ(g)) = 0`.

## Provenance (internal)

This is an internal step of the proof of `RealAnisotropicCompactConnectedStatement`. In
Borel–Tits, *Groupes réductifs* (1965), 14.3, printed p.146, the corresponding step is
that the Zariski closure of the identity component of `G(ℝ)` is `G`. The module replaces it by
global density of rational points and a finite product.
