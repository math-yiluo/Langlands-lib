# Plot-smooth restrictions and characters on infinite adelic points

Module `Langlands.Global.InfiniteAdelicRestrictionSmooth` proves closure properties of the
plot-smooth functions `InfinitePlotSmoothFunctions F G` on `G(F_∞)`. Plot-smoothness is
smoothness along every coordinate-smooth family of points (`GroupScheme.IsPlotSmooth`). It does
not depend on a chosen manifold structure.

## Results

- `mul_mem_infinitePlotSmoothFunctions`: products of plot-smooth functions are plot-smooth, by
  smoothness of multiplication on `ℂ × ℂ`.
- `comp_affinePointsTarget_mem_infinitePlotSmoothFunctions`: for a morphism `j : H → G` and
  points `a, b` of `G(F_∞)`, `m ↦ f(a · j(m) · b)` is plot-smooth on `H(F_∞)` when `f` is.
  Coordinate-smooth families are preserved by postcomposition with scheme morphisms
  (`CoordinateSmooth.postcomp`) and by multiplication (`CoordinateSmooth.mul`).
- `characterNorm_ofInfinite`: for an algebraic character `χ` and `y ∈ G(F_∞)`, the adelic norm of
  `χ` at `y` with trivial finite components is the archimedean norm `IdeleAbsoluteValue.infinite`
  of `χ(y)`. The finite component of the idele `χ(y)` is `1`.
- `mixedNormCharacter`: the archimedean norm as a continuous character of the units of the mixed
  space `ℝ^{r₁} × ℂ^{r₂}`. `mixedNormCharacter_map` evaluates it on the image of a unit of the
  infinite adele ring.
- `contMDiff_log_characterNorm_ofInfinite`: along a coordinate-smooth family `p`, the function
  `x ↦ log ‖χ(p(x))‖` is smooth. The mixed coordinates of `χ(p(x))` are smooth, because the value is
  the evaluation of the regular function `χ^*(T)` on `𝔾_m`
  (`GroupScheme.Gm.affineUnitsEquiv_eq_map`). A continuous character of the units of a commutative
  real Banach algebra is smooth (`contDiffAt_unitsCharacterExtension`, module
  `ArchimedeanCharacterSmoothness`). The logarithm is smooth on positive values.
- `parameterPower_map_ofInfinite_mem_infinitePlotSmoothFunctions`: for a morphism `j : G → H` and a
  complex character parameter `λ` of `H`, `m ↦ j(m)^λ` (`parameterPower`) is plot-smooth on
  `G(F_∞)`. The proof is by induction on `λ ∈ ℂ ⊗ X^*(H)`. For `s ⊗ χ` the function is
  `exp(s log ‖(j ≫ χ)(m)‖)`, by `characterNorm_comp`. Sums give products of exponentials.

## Provenance

Internal: these are the smoothness facts needed to restrict plot-smooth functions to a Levi
subgroup at infinity and to multiply them by modulus characters.
