# The tail Weyl translate of the real alternate Godement integral

This module is the real counterpart of the Library's `ComplexGapWeylRestriction`. Notation as in
`RealGapAlternateRestriction`, with `n = k + q + 1`.

* `tailWeyl k m = diag(1_k, w_m)`, with `w_m` the long Weyl element of `GL_m(ℝ)`.
  `unfoldingWeyl_eq_tailWeyl`: up to the reindexing `(t+1) + m = (t+m) + 1`, `tailWeyl (t+1) m` is the
  Weyl element `ArchimedeanLocal.unfoldingWeyl` of the Library's unequal-rank local integrals.
  `determinant_tailWeyl`: its determinant is `det w_m`; `abs_det_tailWeyl`: its absolute value is one;
  `determinantWeight_tailWeyl`: the Library's determinant weight `determinantWeight c z` at
  `tailWeyl k m` is the character value `η(det w_m)`, for every exponent `z`.
* `realAdjacentGodementCoefficient_mul_right`: for every quotient datum `D` of rank `r`,
  `realAdjacentGodementCoefficient D a Φ U c (g b) =
  determinantWeight c ((r+1)/2) b · realAdjacentGodementCoefficient D a (rectangularTranslate 1 b Φ) U c g`,
  where `rectangularTranslate 1 b Φ (X) = Φ(X b)`. The determinant weight is multiplicative and the
  right translates of the test compose.
* `mul_tailWeyl_left`, `mul_tailWeyl_right`: right multiplication by `tailWeyl k m` fixes the first
  `k` columns and reverses the last `m` columns.
* `reverseTail T` keeps the leading factor of `T` and reverses the order of its `q + 2` column
  factors. `eval_mul_tailWeyl`: `eval T (X · tailWeyl k (q+2)) = eval (reverseTail T) X`.
* `rectangularTranslate_tailWeyl`: if `Φ([A | x]) = squareEval T A · tail_{q+1}(x)` for all `A`, `x`,
  then the right translate of `Φ` by `tailWeyl k (q+2)` is separated in the same way by the factors of
  `reverseTail T`.

`RealGapWeylRestrictionStatement` (proved by `realGapWeylRestriction`): with `a`, `D'`, `η₁`, `κ` as
in `RealGapAlternateRestrictionStatement`, there is `C > 0` such that for every `c`, `T`, every test
`Φ` separated by `squareEval T` and `tail_{q+1}`, every `U ∈ realUniformWhittakerModel (k+q) ds (-a)`
and every `g ∈ GL_k(ℝ)`, the alternate kernel of `reverseTail T` has integrable fibers for
`η = entryHaar μ (q+1)`, its fiber integral is integrable for `σ = outerMeasure k q μ η₁ κ`, and

`realAdjacentGodementCoefficient D' a Φ U c (diag(diag(g, 1_{q+1}), 1) · tailWeyl k (q+2)) =
η(det w_{q+2}) · realAdjacentWeylSign (k+q) c · P g (1/2) · C ·
∫ (∫ alternateRestrictionKernel k q a c (reverseTail T) U g p Z dη(Z)) dσ(p)`.

The proof moves `tailWeyl k (q+2)` into the test by `realAdjacentGodementCoefficient_mul_right` and
applies `realGapAlternateRestriction` to the translated test with the reversed factors. The tail Weyl
element is the Weyl element `w_{n,m} = diag(1_m, w_{n-m})` of the unequal-rank functional equation in
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
