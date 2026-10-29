# Ordered coordinate coefficients for Cartan polynomial expressions

Worker 459 constructed this module. All declarations are in
`Langlands.Global.ArchimedeanGL` and apply to an arbitrary number field
`K : Type u` and every natural rank `n`, including zero.

This is an internal algebraic and differential construction. It imports
the published coordinate-data carrier
`Langlands.Analysis.CoordinateScalarDifferentialOperator` and the actual
Cartan bases and ambient expression through
`Langlands.Global.ArchimedeanCartanAmbientOperator`. The source motivation
is the route recorded in
`notes/automorphic/elliptic-analyticity-source-map.md`: construct actual
finite coefficients before undertaking the separate symbol and analytic
regularity arguments. This recurrence is internal derived content, not
a transcription or proof of a result in Morrey–Nirenberg.

Write `E = ArchimedeanMatrix K n` and `d = Module.finrank ℝ E`.
The domain throughout is the existing real normed matrix space over the
mixed real and complex infinite places. Its matrix operator norm and
topology are retained.

`cartanCoordinateBasis` fixes Mathlib's `Module.finBasis ℝ E`, a real
basis indexed by `Fin d` consisting of actual vectors of `E`.
`cartanCoordinateEquiv` is this basis's continuous linear coordinate
equivalence from the original normed space to `Fin d → ℝ`.
`cartanCoordinateFunctional j` is its `j`-th coordinate projection.
Only the algebraic basis is chosen; no operator is selected from an
existence assumption. The coefficient recursion below uses the same
basis for every order and every polynomial.

`CartanCoordinateCoefficients r` is the array type

```text
(k : Fin (r + 1)) → (Fin k.val → Fin d) → E → ℂ.
```

Thus a word is ordered and may repeat a letter. Coefficients are actual
complex functions on the original domain. The function
`cartanCoefficientExtend a k w y` reads `a` if `k ≤ r` and returns
zero otherwise. The two extension lemmas prove these branches directly
from the definition. No derivative order above the old declared bound
is accessed.

For a field `V : E → E`, write `v_j(y)` for the real number
`cartanCoordinateFunctional j (V y)` and write `ā` for the zero
extension of `a`. The array
`cartanLeftDirectionalCoefficients a V`, of declared order `r + 1`,
is the following explicit recurrence:

```text
b_k(w,y) =
  (if k ≤ r then (fderiv ℝ (a_k(w,·)) y)(V(y)) else 0)
  + (if k = 0 then 0
     else ā_(k-1)(tail(w),y) * (v_(w(0))(y) : ℂ)).
```

In Lean the second term is the natural-number recursion
`cartanPrependCoefficient`: its zero case is zero; its successor case
uses `w 0` and the tail `fun j => w j.succ`. The new direction is
prepended, with the first letter of the new word selecting its field
coordinate. The other term differentiates the old coefficient as a
function of the base point. Every Fréchet derivative is taken over
`ℝ`, with complex codomain. Mathlib's total `fderiv` defines this
expression without smoothness premises; the construction uses no
regularity oracle.

For every index `i : CartanBasisIndex K n`,

```text
cartanMatrixField i y =
  y * realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i).
```

The full published real Cartan basis is used. Its compact and
complementary directions, including both real directions at each complex
place, are all present. `cartanSquareSumCoefficients a` takes two
successive left directional coefficient compositions with this same
field for each `i`, then sums the resulting arrays over the entire
Cartan index. Its declared order is `r + 1 + 1`. In particular, a second
composition differentiates the coefficient functions created by the
first composition, which contain the varying field coordinates.

`cartanIdentityCoefficients` has declared order zero and coefficient
one at its unique order and unique empty word.
`cartanIterateCoefficients m` has declared order `2 * m`. Its zero
case is the identity array. Its successor applies
`cartanSquareSumCoefficients` to the preceding array. The result is read
through zero extension at each target word. The old bound is
`2 * m + 1 + 1`, equal to the target bound `2 * (m + 1)`, so this
read introduces no truncation; it avoids dependent casts in the
implementation. Outside the declared bound, the extension is still zero.

For `p : Polynomial ℂ`, the final declaration is

```text
cartanPolynomialCoordinateOperator K n p :
  Langlands.Analysis.CoordinateScalarOperator E d (2 * p.natDegree).
```

Its basis is the fixed `cartanCoordinateBasis`. Its coefficient at
`k,w,y` is the finite support sum

```text
Σ_(m ∈ p.support) p.coeff m *
  cartanCoefficientExtend (cartanIterateCoefficients m) k w y.
```

The implementation uses `Polynomial.sum`. Each summand is zero at word
lengths greater than `2 * m`; the target retains every length up to
`2 * p.natDegree`. A nonzero coefficient has `m ≤ p.natDegree`, so this
is padding to the common order bound. Polynomial coefficients multiply
the already constructed coefficient functions.

All definitions include degree zero, the zero polynomial, an empty
coordinate basis and rank zero. A constant polynomial has only the
identity-iterate term, at declared order zero. The zero polynomial has
empty support and hence all coefficients zero, also at declared order
zero; `cartanPolynomialCoordinateOperator_zero_coefficient` proves this
by simplifying the defining sum. If the Cartan index is empty, each
square-sum successor is an empty sum and thus zero. No nonzero vector
or positive rank is required.

The basis equality lemma is definitional. The final Lean `example`
checks the complete unapplied telescope, including arbitrary universe,
field and number-field instances, all ranks and every complex polynomial.

This module constructs coefficient data only. It does not assert that
the carrier's action equals an ambient iterate or a genuine enveloping
action, nor prove a highest-order symbol formula, coefficient
analyticity, ellipticity or analytic regularity. Those comparisons and
proofs require a separate focused unit. The imported carrier contains
only the basis and actual coefficients; no annihilation or analytic
solution certificate is added.
