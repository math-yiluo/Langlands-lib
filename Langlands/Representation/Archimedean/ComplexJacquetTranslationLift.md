# Tuples of principal-series functions indexed by `k`-subsets

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetTranslationLift`, namespace
`Langlands.Archimedean.JacquetTranslation`.

This module holds no statement definition. It models the `(𝔤, K)`-module `X(d) ⊗ Λ^k ℂ^n`
(holomorphic) or `X(d) ⊗ Λ^k ℂ̄^n` (antiholomorphic) as tuples of functions, and decomposes
tuples into lifts of functions of shifted principal series. It is used by
`ComplexJacquetTranslationProof`. All content is internal.

Notation: `X(d)` is `KX d`, the `U(n)`-finite functions of `complexStandardModule n (List.ofFn d)`
(the principal series `principalSeries ℂ n (complexPositionCharacter (List.ofFn d))`). The flag
`anti : Bool` selects the holomorphic (`false`) or antiholomorphic (`true`) side; `mm anti` are
the corresponding minors (module `ComplexJacquetTranslationMinors`).

## Shifted characters

- `fac anti z` is `z` or `z̄`; `eps anti` is `1` or `-1`.
- `shiftChar anti d S` replaces `d j`, for `j ∈ S`, by the character with weight
  `l(d j) + eps anti` and exponent `t(d j) + 1/2` (`characterOfParams`), and keeps `d j` for
  `j ∉ S`. `shiftChar_weight` and `shiftChar_exponent` state this coordinatewise.
- `borelFactor_shift` and `principalSeriesCharacter_shift`: the principal-series character of
  the shifted characters at `diag(a)` is that of `d` times `∏_{r ∈ S} fac anti (a r)`.

## Tuples and components

A tuple is `F : Sub n k → GL_n(ℂ) → ℂ`, with every `F T ∈ X(d)`.

- `piS anti F S (g) = ∑_T mm anti g S T · F T (g)` is the `S`-component.
- `piS_borel`: under left multiplication by `diag(a) u` (`u` upper unipotent),
  `piS anti F S (diag(a) u g) = χ_d(a) ∑_U mm anti (diag(a) u) S U · piS anti F U (g)`.
- `mm_borel_self`, `mm_borel_eq_zero`: for the upper triangular matrix `diag(a) u`, the diagonal
  minors are `∏_{r ∈ S} fac anti (a r)`, and `mm anti (diag(a) u) S' S = 0` when
  `wt S ≤ wt S'` and `S' ≠ S` (from `minorMat_upper_ne_zero`).

## Lifts

- `liftK anti h S T κ = h(κ) · mm anti κ* T S` on `U(n)`.
- `exists_lift`: for `h ∈ X(shiftChar anti d S)` and every `T` there is `f ∈ X(d)` with
  `f = liftK anti h S T` on `U(n)`. This is the Library's extension theorem
  `complexPrincipalSeriesExtension`; its hypotheses are continuity, translate-finiteness
  (`isTF_restrict`, `isTF_mm_star`, products and sums of translate-finite functions), and the
  equivariance `liftK_phaseMatrix_mul` under the diagonal unitary torus, which uses
  `principalSeriesCharacter_shift` and `fac(z) fac(z̄) = 1` for `|z| = 1`.
- `lift anti d S h T` is such an `f` (chosen; `0` if `h ∉ X(shiftChar anti d S)`).
  `lift_mem`, `lift_unitary`, and, since principal-series functions are determined by their
  values on `U(n)` (`eq_of_eq_unitary`), `lift_add` and `lift_smul`.
- `piS_lift_unitary`: on `U(n)` the components of `lift S h` are `h` at `S` and `0` elsewhere
  (`mm anti κ · mm anti κ* = mm anti 1 = 1`).
- `piS_lift`: on all of `GL_n(ℂ)`, `piS anti (lift S h) U = h` if `U = S` and `0` if `U ≠ S`
  and `wt S ≤ wt U`. Proof: write `g = diag(a) u κ` (Iwasawa decomposition,
  `ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary`) and use `piS_borel`,
  `piS_lift_unitary`, `mm_borel_self` and `mm_borel_eq_zero`.

## Decomposition of tuples

- `exists_component`: each component `piS anti F S` agrees on `U(n)` with some
  `h ∈ X(shiftChar anti d S)` (again `complexPrincipalSeriesExtension`; the equivariance is
  `piS_borel` with `mm_diagUnits`).
- `eq_sum_lift`: if `h S` are such functions for all `S`, then `F T = ∑_S lift S (h S) T` for
  every `T`. Both sides lie in `X(d)`; on `U(n)` the right side is
  `∑_S ∑_{T'} mm κ S T' F T'(κ) mm κ* T S = ∑_{T'} mm (κ* κ) T T' F T'(κ) = F T(κ)`.

## The Lie algebra action on tuples

- `act anti X F T = R(X)(F T) + ∑_{T'} Dco anti T T' X · F T'`: the action of the real direction
  `X` on `X(d) ⊗ Λ^k`. `act_mem`: it preserves tuples of `X(d)`
  (`rightDerivative_mem_kFiniteFunctions_principalSeries`).
- `rightDerivative_finset_sum`: right derivatives of finite sums of smooth functions.
- `piS_act`: `piS anti (act anti X F) S = R(X)(piS anti F S)`, the components intertwine the
  action on tuples with right derivatives. Proof: the product rule
  (`ComplexTemperedComplement.rightDerivative_mul_fun`) and `rightDerivative_mm`.
