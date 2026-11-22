# Recovery of the real equal-rank normalized equation for column generators

This module is the real counterpart of the published complex module
`ComplexLocalEqualGeneratorTrace`. Notation:

* `t` with smaller rank `m = t + 1` and larger rank `n = t + 2`; `D`, `D'` real quotient data of
  ranks `t`, `t + 1`; `a` a nonzero real and `e` a parity;
* real character lists `cs`, `fs` of lengths `m`, `n`, with `ds = cs.map character` and
  `es = fs.map character`;
* `χ_z = charData e z`, the character `x ↦ sgn(x)^e |x|^z`;
* `den(xs, ys)` the reciprocal real pair `L`-factor, `ε(xs, ys; b, c)` the real pair `ε`-factor,
  `det(xs, -1)` the determinant character of a block list at `-1`, and `c = √|a|`.

## Helper statements

* `character_minusOne_pow_mul_self`: `d(-1)^(t+1)` squares to one.
* `charData_character_neg_one`: `χ_z(-1) = (-1)^e`, independent of `z`.
* `godementLeadingFamily_eq_recursive`: for `U` in the uniform model with character `-b` there is
  `s₀ > 0` with `godementLeadingFamily D b Φ U p g z = s₀ · χ(-1)^(t+1) · equalRecursiveCoefficient b D Φ U _ χ g`
  for every `p`, `z` and `g`, where `χ = charData p z`. The proof uses the Library's
  `realGodementColumnQuotient` and `χ(-1)^(2(t+1)) = 1`.
* `realEqualIntegral_const_mul` and `realEqualDualIntegral_const_mul`: the equal-rank integral
  and its dual are linear in the first coefficient.
* `stripGrowth_realPairEpsilon_reflect`: `s ↦ ε(1 - s + z)` is bounded on vertical strips.
* `Langlands.Archimedean.realRank_map_character`: the real rank of a character list is its length.

## Statement

`RealLocalEqualGeneratorTraceStatement t` assumes:

* `U` in the uniform model of `ds` with character `a`;
* a uniform Whittaker map `B` for `es` with character `-a` that has a continuous Whittaker
  evaluation, a standard vector `f`, and the larger coefficient `V = B f`;
* a compact set `S` of full-row-rank `m × n` matrices and a Schwartz test `Φ` vanishing off `S`;
* a Schwartz function `φ` on `ℝ^n`.

It also assumes two inputs.

1. (Corank one.) For every `V'` in the uniform model of `es` with character `-a`, the corank-one
   integral of `(V', U)` and its dual with parameter `-a` satisfy `HasRealPairNormalizedGrowth`.
   The lists are `es, ds` with duals, the `ε`-parameter is `a`, the scale `√|a|`, and the sign
   `det(es, -1)^(t+1) det(ds, -1)`. This is Worker 1050's adjacent character predicate at rank `t`
   for these lists.
2. (Matrix.) `RealMatrixCoefficientNormalizedGrowth` holds for every orthogonal-finite square
   test, with lists `[χ_0], es` and duals, parameter `-a`, scale `√|a|` and sign `1`.

It concludes for every leading exponent `z`. Let `L(z) = godementLeadingFamily D (-a) Φ U e · z`
be the column generator. The real equal-rank integral `realEqualIntegral D' (L z) V φ` and its
dual `realEqualDualIntegral (-a) D' (L z) V φ` satisfy `HasRealPairNormalizedGrowth` with:

* lists `χ_z :: ds` and `es`, and their duals;
* `ε`-parameter `-a` and scale `√|a|`;
* sign `det(χ_z :: ds, -1)^(t+1)`.

This is the form of Worker 1050's equal character predicate at rank `t + 1`.

## Proof

1. Apply `realLocalEqualSquareLimit` (from `RealLocalEqualSquareLimit`) to the square test
   `Ψ = equalSquareSchwartz Φ φ`. It gives a function `A(z, s)`, holomorphic along holomorphic
   curves and with strip growth, whose primal and reflected dual traces on fixed chambers are
   the normalized unfolded integrals.
2. On the primal chamber, intersected with the joint-integrability chamber of
   `exists_uniformModel_equalKernel_chamber`:
   * the published unfolding `realLocalEqualUnfolding` identifies the unfolded integral with
     `scale · realEqualIntegral D' (R z) V φ`, where `R z` is the recursive coefficient and
     `scale` is the Haar comparison constant of `realGodementColumnQuotient` at rank `t + 1`;
   * `godementLeadingFamily_eq_recursive` with linearity gives
     `R z = (s₀ C)⁻¹ L z`, where `C = (-1)^{e(t+1)}`.

   Hence `A = Z` with
   `Z(z, s) = scale (s₀C)⁻¹ · den(es, ds)(s) · den([χ_0], es)(s + z) · realEqualIntegral D' (L z) V φ s`.
3. On the dual chamber the published dual unfolding `realLocalEqualDualUnfolding` applies, with
   the square Fourier identity `realLocalEqualSquareFourier` and `charData_inverse`. It gives
   `A(z, 1 - s) = Zd(z, s)`, where `Zd` is the dual integral of `L z` times the dual denominators,
   the factor `C⁻¹ scale (s₀C)⁻¹`, and the inverse of the nonvanishing reflection factor
   `Ph(z, w) = signA · ε(es, ds; a)(w) · ε([χ_0], es; -a)(w + z)`.
4. `Z` and `Zd` are holomorphic on `ball(0, R) × {Re s > σ}` for every `R`. This uses
   `realLocalEqualGeneratorFamily` (from `RealLocalEqualGeneratorFamily`), entire reciprocal
   `L`-factors, and `differentiable_realEpsilon`. The Library theorem
   `Langlands.Analysis.affineTraceRecovery` then gives, for each `z`, a half-plane on which
   `A(z, s) = Z(z, s)` and `A(z, 1 - s) = Zd(z, s)`.
5. For fixed `z`, put `N(s) = κ⁻¹ A(z, s)` and `Nd(s) = κ_d⁻¹ Ph(z, 1 - s) A(z, 1 - s)`, where `κ` and
   `κ_d` are the constants above. Both are entire with strip growth (`stripGrowth_reflect'`,
   `stripGrowth_realPairEpsilon_reflect`).
   * The primal half-plane identity combines `Z` with `realPairLFactor_equal_pair` (from
     `RealLocalEqualNormalizedFactors`).
   * The dual one uses the same lemma for `χ_{-z}` and the dual lists (`dualBlock_charData`,
     `map_dualBlock_character`).
   * The pointwise equation `Nd(1 - s) = C · Ph(z, s) · N(s)` becomes the stated sign and
     `ε`-factor via `realPairEpsilon_charData_shift`, the Library commutation
     `realPairEpsilon_comm`, and `equal_epsilon_coefficient`.

## Provenance and scope

This is Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.2, pp. 55–58. There the
functional equation for the equal-rank integral of a Godement section is obtained from the
unfolded integral (8.1), using the product of the corank-one and matrix functional equations
((8.2) and its reflected counterpart, pp. 57–58). Jacquet claims on p. 55 that (8.1) converges
absolutely for `Re s` large and all exponents in a relatively compact set. That claim fails in
general: see the rank-two example in `RealLocalEqualJointIntegrability.md`. The Lean proof
therefore identifies the raw unfolded traces with the ordinary integrals only on dominant
chambers, where the leading exponent `Re z` (or `Re(-z)` on the dual side) is large. It then
reaches every leading exponent by the identity theorem `affineTraceRecovery`, applied to the
ordinary traces, which are holomorphic in `(z, s)`. The Lean statement
concerns only the column generators (compact full-row-rank tests) and real character lists. It
keeps three explicit inputs: the continuous Whittaker evaluation of `B` (the Library supplies
it only for irreducible standard modules, under the Casselman–Wallach extension premise), the
corank-one normalized equation (the induction hypothesis), and the matrix normalized equation.
It does not treat arbitrary uniform coefficients. That requires the span of the generators and
the comparison of the given model with the canonical range (Worker 771). It does not prove
`RealLocalUniformPositiveEqualContinuationStatement`.
