# The square factor of the real adjacent-rank expansion

Write `H = GL_(r+1)(ℝ)`, `ι` for the inverse transpose on `H`, and let `D` be real quotient
measure data of rank `r` with Haar measure `D.groupHaar` on `H`. For a real character datum `c`,
a square Schwartz test `F` and `s ∈ ℂ`, `realAdjacentMatrixWeight c F s z` is
`F(z) c(det z) |det z|^(s + r/2)`. The module proves the normalized functional equation of the
square integrals that appear as the second factors in the finite expansion of the real
adjacent-rank integral.

## Results

- `realMatrixZetaKernel_detCharacter` and
  `realMatrixZetaKernel_detCharacter_inverseTranspose`: the kernel of
  `GodementJacquet.realMatrixZeta` for the coefficient `g ↦ c(det g) C(g)` (respectively its
  composite with `ι`) is `realAdjacentMatrixWeight c F s z · C(z)` (respectively the weight of
  the inverse character `c⁻¹` times `C(ι z)`), since `det ι(z) = (det z)⁻¹`.

- `realAdjacentSquareGrowth`. Let `K` be a compact group with a finite measure `μK`, `iK : K → H`
  a continuous homomorphism into the orthogonal group, `w` a continuous weight on `K`, `a ∈ ℝˣ`,
  `c` a real character datum, `F` a square Schwartz test, `fs` a list of `r+1` real character data
  and `f` a compact-finite standard vector of the character list `fs`. Put
  `C(z) = ∫_K w(k) f(iK(k) z) dμK(k)`. Then:
  1. on some right half-plane the functions `z ↦ realAdjacentMatrixWeight c F s z · C(z)` and
     `z ↦ realAdjacentMatrixWeight c⁻¹ F̂ s z · C(ι z)` are `D.groupHaar`-integrable, where
     `F̂ = RealGodement.realRectangularSchwartzFourier a F`;
  2. the integrals of these two functions over `H` satisfy `HasRealPairNormalizedGrowth` for the
     lists `[character c]` and `fs`, their blockwise duals, the epsilon parameter `a`, the scale
     `√|a|` and the sign `1`.

## Proof

`C(g)` is the compact pairing `compactPairing` of `RealAdjacentCompactProjection` evaluated on
the right translate by `g` of the included standard vector (`compactPairing_translate`), and
this pairing has a compact derivative bound (`hasCompactDerivativeBound_compactPairing`). The two
kernel identities above rewrite the square integrals as the real matrix zeta integrals of the
coefficient `c(det g) C(g)` with `F` and of its composite with `ι` with the transform
`RealSquareFourier.matrixTransform a F`, which equals `F̂` pointwise
(`GodementJacquet.matrixTransform_eq_realRectangularSchwartzFourier`). The convergence statement
is the integrability clause of `GodementJacquet.realMatrixPairIdentity_expand`, and the
normalized equation with strip growth is `GodementJacquet.realMatrixPairNormalizedGrowth`
of `RealMatrixNormalizedGrowth`, both applied to the expanded list of `fs`. For a character list
the expanded list is the list itself (`RealGodement.expand_map_character`), and
`RealGodement.hasRealPairNormalizedGrowth_list_congr` transports the conclusion along this
equality.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`. The opening of §4.7 (p. 30) states that the matrix
integral `Z` of a compact-pairing matrix coefficient is a holomorphic multiple of the product of
`L`-factors, bounded at infinity in vertical strips, and Proposition 4.4 (p. 31) gives the matrix
functional equation for a coefficient defined by a continuous linear form. In §8.3 (p. 60) these
are applied to the square factor `Z(s + u_n, f_i ⊗ μ_n, Φ₁)` of each term of the expansion, a
holomorphic multiple of `∏_j L(s + u_n + v_j, μ_n ν_j)`. The formal statement replaces the
holomorphic-multiple and boundedness assertions by the Library's entire normalization with
exponential growth on vertical strips; the exponent `u_n` is part of the character datum `c`.
