# Growth of the constant terms of a family with uniform moderate growth

Module `Langlands.Global.AdelicUniformTemperednessGrowth`, namespace
`Langlands.Global.StandardParabolicFamily`.

Throughout, heights `‖g‖` on `G(𝔸)` are defined by a matrix representation
`rho : MatrixRepresentation G (Fin N)` of size `N > 0`; every result below except
`adelicIteratedDirectionalValue_sub` assumes `N > 0`.

## Results

- `adelicIteratedDirectionalValue_sub`: a word of real right-orbit derivatives
  (`adelicIteratedDirectionalValue`) commutes with the difference of two functions that are
  smooth on every archimedean slice. The derivatives act linearly on the smooth functions on
  `G(F_∞)` (`manifoldSmoothFunctions`), and the adelic derivative is the slice derivative
  (`adelicDirectionalValue_pair`).
- `rpow_adelicSourceNorm_le`: let the matrix representation `rho` have size `N > 0`. Then
  `‖g‖_src^R ≤ c^{-R} ‖g‖^{max R 0}`, where `‖g‖ = c ‖g‖_src`
  (`adelicHeight_eq_scalar_mul_sourceNorm`, `c = N^{∑ mult} > 0`) and `‖g‖ ≥ 1`
  (`one_le_adelicHeight`, which needs `N > 0`).
- `constantTerm_family_growth`: let `f` be a family with uniform moderate growth of exponent `R`
  on `S` at an open level `L` (`IsUniformGrowthFamily`). Then for every standard index `Q`, the
  constant terms `C_Q (f x)` are smooth on archimedean slices. For every word `s` there is one
  `C` with `‖D_s C_Q (f x) (g)‖ ≤ C ‖g‖^{max R 0}` for all `x ∈ S` and `g`. The derivatives of
  `f x` are given by the enveloping-algebra action (`evaluate_adelicDirectionalWordEnveloping`)
  and bounded by the growth hypothesis. `adelicConstantTermDirectionalGrowth` then passes the
  bounds to the constant terms along the radical `U_Q`.
- `exists_height_rpow_le`: let the matrix representation `rho` defining the height have size
  `N > 0` and let `R' ≥ 0`. There is `K ≥ 0` such that for every compact `Ω` there is `M ≥ 0`
  with `‖t k‖^{R'} ≤ M e^{K ‖t‖}` for positive `t` of the maximal split torus and `k ∈ Ω`
  (`TorusFrame.exists_height_le` and `adelicHeight_mul_le`). The rate is `K = r R'`, where
  `r ≥ 0` is the rate of the height bound `ht(t) ≤ C e^{r ‖t‖}`; it does not depend on `Ω`, and
  it is nonnegative because `R' ≥ 0`.
- `family_growth_bounds`: the two growth hypotheses `hgr` and `hdgr` of
  `constantTerm_chamber_bound` hold for the family `x ↦ (f x).val`. For `hdgr`, the step is a
  difference of two constant terms, and `adelicIteratedDirectionalValue_sub` reduces its
  derivatives to theirs. There are finitely many standard indices and finitely many words of a
  given length, so one constant serves for all of them.

## Source

Bernstein–Lapid's uniform growth of Eisenstein series enters through `IsUniformGrowthFamily`; the
transfer of growth to constant terms is the standard estimate (Mœglin–Waldspurger 1995, I.2.6)
in the form of `adelicConstantTermDirectionalGrowth`.
