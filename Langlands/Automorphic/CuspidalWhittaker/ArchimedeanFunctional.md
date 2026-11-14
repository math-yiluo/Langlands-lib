# Whittaker functionals at the archimedean places of a cuspidal realization

Module `Langlands.Automorphic.CuspidalWhittaker.ArchimedeanFunctional`, namespace
`Langlands.Automorphic.CuspidalWhittaker`. Worker 174 wrote it for the proof of
`Langlands.Automorphic.CuspidalArchimedeanWhittakerFunctionalStatement` (Task 5996,
`e3f48d66-76bc-4321-a8ea-e25681c89d3f`, published under Task 5720).

Let `F` be a number field and `S` an operator realization of `GL_{r+1}` over `F`. For
`x ∈ S` and `h ∈ GL_{r+1}(𝔸_F)`, `W_x(h)` is the Library's iterated Whittaker coefficient
`descend r` of the realized form `evaluate (S.toContinuous x)`, evaluated at `h`. The module
shows how the linear form `ℓ_h : x ↦ W_x(h)` changes under a real Lie direction whose matrix
squares to zero. Write `A ∈ GL_{r+1}(ℝ^{r₁} × ℂ^{r₂})` for the archimedean component of `h`
in mixed coordinates (`archimedeanGLCoordinates`), and `M` for the matrix of a direction
`Y` of the real Lie algebra (`realLieAlgebraToMatrix`).

## Square-zero exponentials and conjugation

- `exp_smul_of_mul_self_eq_zero`: if `M * M = 0` then `exp(s M) = 1 + s M`. The exponential
  series (`NormedSpace.exp_eq_tsum`) has only its first two terms nonzero
  (`tsum_eq_sum` over `range 2`, since `M^(m+2) = 0`).
- `mul_ofInfinite_mul_inv`: `h · c · h⁻¹ = c'` for an infinite adelic element `c`, where
  `c' = h_∞ c h_∞⁻¹` sits at the infinite places and the finite component is `1`. Checked on
  the infinite and finite components (`AdelicGL.ext_infinite_finite`).
- `ofInfinite_val_apply`: the entries of an infinite element viewed adelically are pairs of
  its infinite entries and the identity entries at the finite places.
- `coordinates_conj_oneParameter`: for `M * M = 0`, the mixed coordinates of
  `a · exp(s Y) · a⁻¹` are `1 + s · A M A⁻¹`, with `A` the coordinates of `a`.
- `conjDirection h Y` is the matrix `A M A⁻¹` (a definition for this proof; internal).

## Upper unitriangular infinite elements

- `superSum_ofInfinite`: the Library's `superSum 0` of an infinite element `c` (the sum of
  its superdiagonal entries) is `(∑ᵢ c_{i,i+1}, 0)` in `𝔸_F = 𝔸_∞ × 𝔸_f`.
- `isUpperColId_ofInfinite`: if the mixed coordinates of `c` agree with the identity on and
  below the diagonal, then `c`, viewed adelically, is upper unitriangular in the sense of
  the Library's `IsUpperColId 0`. The ring isomorphism to the mixed space is injective, and
  the finite component is `1`.
- `infiniteTrace_superdiagonal_conj`: for `M * M = 0`, the infinite trace of
  `∑ᵢ (h_∞ exp(s Y) h_∞⁻¹)_{i,i+1}` is `s · mixedTrace(∑ᵢ (A M A⁻¹)_{i,i+1})`. It follows
  from `coordinates_conj_oneParameter`, since the superdiagonal of `1` is zero and the
  Library's `infiniteTrace` is `mixedTrace` after the isomorphism to the mixed space.

## The derivative formula for Whittaker coefficients

`descend_eq_of_hasCurveDeriv` (function form). Assume:

- `F` has compact adele quotient;
- `Φ` and `Ψ` satisfy the Library's level properties `LevelProps r`;
- `M * M = 0`, and `N = A M A⁻¹` vanishes on and below the diagonal;
- `e(s) = exp(s Y)` as an infinite adelic element, and `HasCurveDeriv e Φ Ψ` (module
  `CurveDerivative`).

Then `descend r Ψ h = 2π i · mixedTrace(∑ᵢ N_{i,i+1}) · descend r Φ h`.

Proof. Write `τ = mixedTrace(∑ᵢ N_{i,i+1})`.

1. By `HasCurveDeriv.descend` at the point `h` and time `0`, with `e(0) = 1`, the map
   `s ↦ descend r Φ (h · e(s))` has derivative `descend r Ψ h` at `0`.
2. Write `h · e(s) = (h e(s) h⁻¹) · h`. The element `h e(s) h⁻¹` is infinite, with
   mixed coordinates `1 + s N`. Since `N` is strictly upper triangular, it is upper
   unitriangular.
3. The level-`0` equivariance of `descend r Φ` (`levelProps_descend`, `LevelProps.equivariant`)
   gives `descend r Φ (h · e(s)) = ψ(superSum 0 (h e(s) h⁻¹)) · descend r Φ h`.
4. The superdiagonal sum is infinite (`superSum_ofInfinite`), so the character is
   `unitExp(infiniteTrace …)` (`adelicCharacter_of_integral`). This equals
   `exp(2π i s τ)` by `infiniteTrace_superdiagonal_conj` and `Circle.coe_exp`.
5. The function `s ↦ exp(2π i s τ) · descend r Φ h` has derivative
   `2π i τ · descend r Φ h` at `0`. By uniqueness of derivatives (`HasDerivAt.unique`, after
   `HasDerivAt.congr_of_eventuallyEq`) the two derivatives agree.

## The functional on a cuspidal realization

- `levelProps_realization`: for a cuspidal `S` and `x ∈ S`, the realized form of `x`
  satisfies `LevelProps r`. This is the Library's `levelProps_top`, with the vanishing of
  constant terms `OperatorRealization.constantTerm_eq_zero`.
- `realizationFunctional S hS h : Module.Dual ℂ S.Space` is `x ↦ W_x(h)`
  (`realizationFunctional_apply`). A definition for this proof (internal), following the
  Library's finite-place `LocalFunctional.whittakerFunctional`. Additivity is the Library's
  `descend_add`, and homogeneity is `descend_const_mul`.
- `realizationFunctional_lieOperator` (Lemma C): for `M * M = 0` and `N = A M A⁻¹` strictly
  upper triangular, `ℓ_h(Y · x) = 2π i · mixedTrace(∑ᵢ N_{i,i+1}) · ℓ_h(x)`, where `Y · x`
  is the Library's `S.lieOperator Y x`. It is `descend_eq_of_hasCurveDeriv` with
  `Φ = W_x` and `Ψ = W_{Y·x}`. The curve hypothesis is the Library's
  `OperatorRealization.hasDerivAt_evaluate_oneParameter`.

## Lean notes

The module declares local `AddCommGroup` instances (as `Submodule.addCommGroup`) for the
Library's function spaces and for `S.Space`, as the Library's `CuspidalUnitaryForm` does. The
derivative formula is stated over abstract `Φ`, `Ψ` and a curve `e` with
`e s = exp(s Y)` given as a hypothesis. Rewriting directly in the realization's types timed
out.
