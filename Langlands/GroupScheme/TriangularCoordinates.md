# Triangular polynomial coordinates on affine group schemes over a field

## Definitions

Let `F` be a field and `U : GroupScheme (Spec (CommRingCat.of F))` an affine group scheme
over `F` (`[IsAffine U.X.left]`). Its coordinate ring is the global-section ring
`AffineCoordinateRing F U.X = Γ(U, ⊤)` with its `F`-algebra structure. For an `F`-algebra
`A`, the points `U.affinePoints A` form the group `U(A)`. A global function `t` takes the
value `U.affinePointEvaluation A x t ∈ A` at a point `x ∈ U(A)`; below this value is
written `t(x)`.

`HasTriangularCoordinates U` states that there exist a natural number `d`, global functions
`t : Fin d → AffineCoordinateRing F U.X` and polynomials
`P : Fin d → MvPolynomial (Fin d ⊕ Fin d) F` such that:

1. **Polynomial coordinates.** The `F`-algebra map
   `MvPolynomial.aeval t : F[X₀, …, X_{d-1}] → AffineCoordinateRing F U.X`, which sends
   `X_i` to `t i`, is bijective. So `t` identifies `U` with affine `d`-space as an
   `F`-scheme.
2. **Triangularity.** Every variable occurring in `P i` (`(P i).vars`) is `Sum.inl j` or
   `Sum.inr j` with `j < i`.
3. **Group law.** For every `F`-algebra `A : CommAlgCat.{u} F`, all points `x y ∈ U(A)` and
   every index `i`,

   `t_i(x * y) = t_i(x) + t_i(y) + P_i(t(x), t(y))`.

   Here `P_i` is evaluated with `Sum.inl j ↦ t_j(x)` and `Sum.inr j ↦ t_j(y)`.

For `d = 0` the conditions say that the coordinate ring is `F`, so `U` is the trivial group.

`UnipotentTriangularCoordinatesStatement` is the proposition that, for every field `F` of
characteristic zero in universe `u`, every affine group scheme `U` over `F` that is locally
of finite type, smooth (`Smooth U.X.hom`), connected (`ConnectedSpace U.X.left`) and
unipotent (`IsUnipotent U`) satisfies `HasTriangularCoordinates U`. The module states this
proposition but does not prove it.

`IsUnipotent U` is the published Library predicate
(`Langlands/GroupScheme/Reductive/Basic.lean`). It requires that every matrix representation
of `U` on `F^n`, for a nonempty finite index type `n`, has a nonzero fixed vector. This
is Milne's definition: "an algebraic group G is unipotent if every nonzero representation
of G has a nonzero fixed vector". Milne notes that it suffices to check this for
finite-dimensional representations.

## Source and provenance

The definition `HasTriangularCoordinates` is internal. It isolates the algebraic input that
the adelic compactness argument in `Langlands.Global.TriangularRationalQuotientCompact`
needs.

The proposition `UnipotentTriangularCoordinatesStatement` is derived from J. S. Milne,
*Algebraic Groups* (Cambridge, 2017), registered source `milne-2017-algebraic-groups`,
SHA256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, Chapter 14,
§14.d ("Unipotent algebraic groups in characteristic zero"). In Milne, an algebraic group
is a group scheme of finite type over `k`, and all algebraic groups in Chapter 14 are
affine. The definition of unipotent is in §14.b, printed page 280 (PDF page 296).

- Proposition 14.32 (printed page 289, PDF page 305): for every unipotent algebraic group
  `G` over a field `k` of characteristic zero, the exponential map `exp : Lie(G)_a → G` is
  an isomorphism of schemes.
- 14.34 (printed page 290, PDF page 306): nilpotent Lie algebras and their filtrations
  `g = a₀ ⊃ a₁ ⊃ ⋯ ⊃ a_r = 0` by ideals with `[g, a_i] ⊂ a_{i+1}`.
- 14.35 (printed pages 290–291): the Campbell–Hausdorff series
  `H(U, V) = Σ_m H_m(U, V)`, with `H_1 = U + V`. For `m ≥ 2`, `H_m` is a rational linear
  combination of iterated brackets of length `m` in `U` and `V`.
- Proposition 14.36 (printed page 291, PDF page 307):
  `exp(x) · exp(y) = exp(H(x, y))` for all `k`-algebras `R` and all `x, y ∈ g_R`.

The derivation is as follows. By 14.31, applied to a faithful representation, `g = Lie(U)`
lies in a strictly upper triangular matrix algebra, so it is nilpotent. Choose a filtration `g = a₀ ⊃ a₁ ⊃ ⋯ ⊃ a_r = 0` as in
14.34. Choose a basis `e₀, …, e_{d-1}` of `g` adapted to it: first a basis of a complement
of `a₁` in `a₀`, then of a complement of `a₂` in `a₁`, and so on. Call `k` the layer of
`e_i` when `e_i` is in the complement of `a_{k+1}` in `a_k`. Indices increase with the
layer. Let `t_i` be the `i`-th coordinate of `exp⁻¹`. Proposition 14.32 gives condition 1.

Now consider an iterated bracket of length `m ≥ 2` whose entries come from layers
`k₁, …, k_m`. It lies in `a_{max k_l + 1}`. So its coordinate along `e_i` vanishes unless
every entry has layer smaller than the layer of `e_i`, and such entries have index `< i`.
Brackets of length greater than `r` vanish, so `H(x, y) - x - y` is a finite sum. Expand it
multilinearly in the coordinates; by 14.36 this expansion holds over every `k`-algebra `R`.
The coefficients of the result combine the rational coefficients of the universal expressions
`H_m` with the structure constants of `g` in the chosen basis, which lie in `k`. The result is
therefore a polynomial `P_i` with coefficients in `k` (in general not in `ℚ`) in the
coordinates of `x` and `y` of index `< i`. For example, over `k = ℚ(√2)` take the strictly
upper triangular `3 × 3` matrices with `e₀ = E₁₂`, `e₁ = √2 E₂₃`, `e₂ = E₁₃` and
`a₁ = k e₂`; then `[e₀, e₁] = √2 e₂` and `P₂ = (√2/2)(x₀ y₁ - x₁ y₀)`. The Lean definition
accordingly takes `P i` in `MvPolynomial (Fin d ⊕ Fin d) F`. This gives conditions 2 and 3. The
derivation does not use the hypotheses `Smooth` and `ConnectedSpace`. They are included so
that the statement matches its downstream use, which assumes them.
