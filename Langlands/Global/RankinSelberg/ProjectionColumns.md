# Character coefficients along block unipotent subgroups, one block at a time

Module `Langlands.Global.RankinSelberg.ProjectionColumns`. It is internal infrastructure for
`ProjectionExpansion`. No literature source is cited for its statements.

## Block unipotent periods (namespace `Langlands.Global.GeneralLinearBlockSemidirect`)

Let `n` be a finite index type and `e, w : n → ℤ` weights with
`hw : ∀ i j, e i ≤ e j → w i ≤ w j`. The Library module `GeneralLinearBlockSemidirectPeriod`
writes the adelic points of `blockUnipotent n F e` as a topological semidirect product. The
normal factor is the coarser `blockUnipotent n F w` (via `normalInclusion`). The complement is
the block Levi part `leviUnipotent n F e w` (via `leviInclusion` and `leviProjection`). The
rational subgroups are compatible.

`normalizedPeriod_eq_iterated` applies `normalizedPeriod_eq_iterated_of_compact` of
`ProjectionPeriod` to this splitting. The hypotheses are compactness of the rational quotients for
`e` and `w`; compactness for the Levi part comes from the Library's
`leviRationalQuotientCompactSpace`. For a continuous function `φ` on the points of the `e`-group,
left invariant under its rational points, the normalized period over the chosen fundamental
domain of the `e`-group equals the normalized period over the Levi fundamental domain of the
normalized periods of `y ↦ φ(normalInclusion y · leviInclusion m)` over the `w`-group.

## Coefficients (namespace `Langlands.Global.RankinSelbergGlobal.Unfolding`)

- `quotientMassNormalizer_toReal`: for a closed subgroup functor `U`, the real normalizer
  `(quotientMassNormalizer F G U).toReal` is the inverse real Haar mass of the chosen fundamental
  domain of `U(F)` in `U(𝔸)`. The proof unfolds the definitions and uses
  `ENNReal.toReal_inv`; no finiteness is needed.
- `subgroupCharacterCoefficient_eq_levi`: transitivity of the Library's character coefficients.
  Its hypotheses are compact rational quotients for `e` and `w`; a continuous multiplicative
  `χ` on the `e`-group, trivial on rational points; and a continuous function `f` on `GL(𝔸)`,
  left invariant under the rational points of the `e`-group. Then
  `subgroupCharacterCoefficient (e, χ) f x` is the real normalized integral, over the Levi
  fundamental domain, of
  `conj χ(leviInclusion m) · subgroupCharacterCoefficient (w, χ ∘ normalInclusion) f (m x)`.
  The proof writes both coefficients as normalized fundamental-domain integrals with
  `subgroupCharacterCoefficient_eq_setIntegral` (module `UnfoldingCoefficient`) and
  `quotientMassNormalizer_toReal`. It applies `normalizedPeriod_eq_iterated` to
  `z ↦ f(z x) conj χ(z)`, then splits `χ(i y · j m) = χ(i y) χ(j m)`.
