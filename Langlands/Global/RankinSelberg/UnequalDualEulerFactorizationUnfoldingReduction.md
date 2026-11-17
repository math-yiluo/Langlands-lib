# The unequal-rank dual Euler factorization from the unfolding statement

Module `Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationUnfoldingReduction`,
namespace `Langlands.Global.RankinSelbergGlobal.UnequalDualEulerContragredient`.

## Main results

`UnequalDualEulerFactorizationUnfoldingReductionStatement` is the proposition

```text
UnequalUnfoldingStatement.{u} → UnequalDualEulerFactorizationStatement.{u, uQ}
```

with the universe parameters `u` (number fields) and `uQ` (spectral presentations) free.
The theorem `unequalDualEulerFactorizationUnfoldingReduction` proves it, and
`unequalDualEulerFactorization_of_unfolding` is the same result as a function of the
premise.

The only premise is the Library statement `UnequalUnfoldingStatement` (module
`Langlands.Global.RankinSelberg.UnequalUnfoldingStatement`). It is used only for the
absolute convergence of the dual integral. The Library's
`UnequalDualEulerFactorizationReduction` has three further premises. Two of them are now
proved in the Library, and their proved content is used here:

- `UnramifiedWhittakerFactorizationStatement`. Its proof module
  `Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof` supplies
  `UnramifiedWhittaker.coefficientMap_eq_smul_of_corner`, which
  `ContragredientDualSplit` uses;
- `WhittakerCellDecompositionStatement`, through the theorem `whittakerCellDecomposition`
  (module `Langlands.Global.RankinSelberg.WhittakerCellDecomposition`).

The third, `ContragredientDualWhittakerStatement`, is open. It is not used. The splitting
of the dual Whittaker functions at unramified places comes instead from
`ContragredientDualSplit.dualWhittaker_split` (module
`Langlands.Global.RankinSelberg.ContragredientDualSplit`).

## Auxiliary results

The notation is that of `UnequalDualEulerFactorizationReduction`: `ι_v(h) =
localPoint F m v h`, `g_v` the component at `v`, `rect(g, y)` the rectangular point,
`w = unfoldingWeyl F h`, `ϖ = placeUniformizer v`, `W°`/`W°⁻` = `sphStd`/`sphInv`,
and `cellFactor h v ψ_v a b s Q = sphInv(diag(Q, I)) · sphStd(Q) · |det Q|_v^(s-(r-t)/2)`.
Throughout, `W̃ = dualFunction (cuspWhittaker F T ψ x)`,
`W̃' = dualFunction (cuspWhittaker F T' ψ⁻¹ x')`, `a` is a tuple of the presented spectrum
of `Pd` at `v` and `b` one of `Pd'`.

- `dualFunction_rectangularPoint_localPoint_mul`: for `g_v ∈ GL_(t+1)(𝒪_v)`,
  `W̃(rect(ι_v(Q) g, y) w) = W°⁻(diag(Q, I); a) · W̃(rect(g, y) w)` for every `y`. It
  combines the first half of `dualWhittaker_split` with the Library's
  `apply_localPoint_mul_of_split` and the support lemma
  `sphericalWhittaker_inverseStandard_rectGL_zero_mul`.
- `dualFunction_localPoint_mul_of_integral`: for `g_v ∈ GL_(t+1)(𝒪_v)`,
  `W̃'(ι_v(Q) g) = W°(Q; b) · W̃'(g)`. It uses the second half of `dualWhittaker_split`
  for `T'`, `Td'` and `Pd'`.
- `dualKernel_localPoint_mul_of_integral`: for `g_v ∈ GL_(t+1)(𝒪_v)`, the dual kernel
  `Unfolding.dualKernel` of `ρ(w)W̃` and `W̃'` at `ι_v(Q) g` is `cellFactor(Q)` times its
  value at `g`. The rectangular inner integral is handled pointwise in `y`, so no
  integrability hypothesis is needed.
- `dualKernel_localPoint_torus_mul` (the cell property): the same with `Q = ϖ^λ`, for
  `g_v ∈ N_(t+1)(F_v) GL_(t+1)(𝒪_v)`. It reduces to the previous lemma through left
  `N_(t+1)(𝔸)`-invariance of the dual kernel
  (`Unfolding.dualKernel_whittaker_unipotent_mul`) and
  `ι_v(ϖ^λ) ι_v(u) = ι_v(ϖ^λ u ϖ^(-λ)) ι_v(ϖ^λ)`.
- `integrand_shift`: the same identity for `dualWhittakerIntegrand` on the classes in
  `unipotentIntegralClasses F (t+1) A`, `v ∉ A`.
- `setIntegral_cons_eq` (the one-place step): if the dual integrand is integrable and
  `L` is the sum of the local terms `localTerm q_v a b s`, then
  `∫_(U_(A∪{v})) = L · ∫_(U_A)`. It applies `whittakerCellDecomposition` at `v` and
  `ϖ`, `integrand_shift` on each cell, and the Library's
  `zpow_modulusExponent_mul_cellFactor`, and concludes by uniqueness of sums.

## Proof

The proof is that of the Library's
`UnequalDualEuler.unequalDualEulerFactorization_of_premises`, with the changes above.
Fix the data of the target. `UnequalUnfoldingStatement` gives `C` such that the dual
integral converges absolutely at `1 - s'` for `Re s' < -C`, that is, at `s` for
`Re s > 1 + C`. `exists_partialEulerFactor_convergence` gives `σ_E` for the Euler product
of `Pd`, `Pd'`. The Satake bounds of `Pd`, `Pd'` (`exists_hasSatakeBound_presentation`)
and `exists_hasSum_localTerm` give `σ_C`. Take `σ = max(1 + C, σ_E, σ_C)`.

For `x`, `x'` spherical outside `S` and `Re s > σ`, the first two conclusions of the
target are these convergence statements. For the identity,
`integral_eq_hasProd_mul_setIntegral` reduces it to the one-place step for every finite
`A ⊇ S` and `v ∉ A`, with factor `partialEulerFactor Pd Pd' v s`. At such `v`,
`FiniteAdditiveSupport` gives `ψ_v` of conductor `𝒪_v`, `ofTuple_surjective` gives the
tuples `a`, `b`, and the local terms sum to
`(∏(1 - a_i b_j q_v^(-s)))⁻¹ = partialEulerFactor Pd Pd' v s` (`exists_hasSum_localTerm`,
`partialEulerFactor_eq`). `setIntegral_cons_eq` is the step.

## Provenance

The statement is internal: it records which premises the proof of the target needs. The
proof follows Cogdell 2004, §4.1, printed p.220 (J. W. Cogdell, *Analytic theory of
L-functions for GL_n*, registered as `cogdell-2004-analytic-theory-gln`, PDF page =
printed page + 3): the dual global integral `Ĩ(1-s; φ̃, φ̃')` factors as the product over
`v ∈ S` of the dual local integrals times `L^S(1-s, π̃ × π̃')`. As in the Library's
`UnequalDualEulerFactorizationReduction`, the unramified dual factor is computed directly.
The ingredients are Shintani's formula (p.206), the dual Whittaker function
`W̃(g) = W(w_n ᵗg⁻¹)` of p.207, the one-place cell decomposition, the local unramified sum
(Theorem 3.3, p.215) and the support lemma of `RectangularSupport`. Cogdell obtains the
factor from the local functional equation instead. This is a deviation in route, not in
statement. The splitting of `W̃` at unramified places is the internal derivation of
`ContragredientDualSplit`.
