# The semilocal numerator from the archimedean numerator

Module `Langlands.Global.Factors.CuspidalPairEisensteinSemilocalNumeratorReduction`.

## Content

- `CuspidalPairEisensteinSemilocalNumeratorReductionStatement.{u}`, in namespace
  `Langlands.Global`, is the proposition

  ```text
  CuspidalPairEisensteinArchimedeanNumeratorStatement.{u} →
    CuspidalPairEisensteinSemilocalNumeratorStatement.{u}
  ```

  The premise is stated in
  [CuspidalPairEisensteinArchimedeanNumeratorStatement.md](CuspidalPairEisensteinArchimedeanNumeratorStatement.md),
  the conclusion in
  [CuspidalPairEisensteinSemilocalNumeratorStatement.md](CuspidalPairEisensteinSemilocalNumeratorStatement.md).
- `cuspidalPairEisensteinSemilocalNumeratorReduction` proves it.
- In namespace `Langlands.Global.CuspidalPairEisensteinSemilocalNumerator`:
  `isOpen_integralOutside`, the set `U_S = integralOutside F r t S` of matrices integral
  outside `S` is open (`RestrictedProduct.isOpen_forall_imp_mem`); `smallAt r t S₀ ε`, the
  matrices `Y` with `|(Y_v)_(ij)|_v < |ε_v|_v` for all `v ∈ S₀` and all entries, and
  `isOpen_smallAt`; `matrixComponent_archimedeanMatrix`,
  `matrixComponent_archimedeanMatrix_add`: matrices with vanishing finite part do not change
  finite components.

The module is a reduction: it does not prove the premise, and so it does not by itself
prove `CuspidalPairEisensteinSemilocalNumeratorStatement`.

## Proof

Fix the data of the conclusion: `F`, `r`, `t`, `T`, `T'` with unitary central characters, a
standard additive character `ψ` and a finite set `S` of finite places.

1. The premise gives a finite set `S₁` of finite places.
   `FiniteTranslation.exists_finiteBox_eq_one`, applied to the continuous `ψ`, gives a finite
   set `T_ψ` and `a_v ≠ 0`, `|a_v|_v ≤ 1`, such that `ψ` is trivial on the adeles with
   archimedean component `0`, integral finite components and `|x_v| < |a_v|` on `T_ψ`. Put
   `S₀ = S ∪ S₁ ∪ T_ψ`; it contains `S` and is chosen before `s₀`.
2. Let `Re s₀ = 0`. The premise gives `φ₀`, a section built from cusp forms spherical
   outside `S₁`, a function `c₀`, meromorphic on `ℂ`, analytic and nonzero at `s₀`, and
   `σ` such that for `σ < Re s` the archimedean integrand of `φ₀` is integrable and its
   integral is `c₀(s)`. The section condition gives an open subgroup `J` of `GL(𝔸_f)` under
   which `φ₀` is right invariant.
3. For every finite place `v`, `FiniteTranslation.exists_ball_openCellUnipotent_mem` gives
   `b_v ≠ 0`, `|b_v| ≤ 1`, with `u'(y)` placed at `v` in `J` whenever `|y_(ij)| < |b_v|`.
   Put `ε_v = b_v a_v`; then `ε_v ≠ 0`, `|ε_v| ≤ |b_v|`, `|ε_v| ≤ |a_v|` and `|ε_v| ≤ 1`.
4. The section is `φ = β φ₀` with the cutoff `β = SemilocalCutoff.cutoff r t S₀ ε`. It is a
   section (`isSection_cutoff_mul`) built from cusp forms spherical outside `S₀`
   (`isSphericalSectionOutside_cutoff_mul`, since `S₁ ⊆ S₀`).
5. Let `C = smallAt r t S₀ ε` and `R = U_(S₀) ∩ C`. `R` is open, contains `0`, is stable
   under adding matrices with vanishing finite part, and its elements have integral finite
   components (at `v ∈ S₀` because `|ε_v| ≤ 1`). The measure comparison
   `ArchimedeanMeasure.exists_setIntegral_comp_archimedeanPart` gives `κ ≠ 0` with
   `∫_R G(Y_∞) dY = κ ∫ G(X) dX` for every almost everywhere strongly measurable `G`.
6. The function is `c = κ · c₀`: meromorphic on `ℂ`, analytic at `s₀` and `c(s₀) ≠ 0`. Let
   `σ < Re s`.
   - By `openCellIntegrand_cutoff_mul` and `inCellAt_openCell_iff`, the integrand of `φ` is
     the integrand of `φ₀` times the indicator of `C`, so
     `I_(S₀)(φ, s) = ∫_(U_(S₀) ∩ C) openCellIntegrand ψ φ₀ s` (`setIntegral_indicator`).
   - For `Y ∈ R`, write `Y = (Y_∞, 0) + Z`, where `Z` has archimedean component `0` and the
     finite components of `Y`. The entries of `Z_v` are integral for every finite `v`, of
     valuation `< |b_v|` at `v ∈ S₁` and `< |a_v|` at `v ∈ T_ψ`. Hence
     `FiniteTranslation.twisted_mul_openCellUnipotent` applies (with `J`, the sphericity of
     `φ₀` outside `S₁`, and step 3), `ψ(Z_(t,0)) = 1` by step 1, and
     `openCellIntegrand_add_of_invariant` gives
     `openCellIntegrand ψ φ₀ s Y = archimedeanOpenCellIntegrand ψ φ₀ s Y_∞`.
   - The archimedean integrand is integrable, hence almost everywhere strongly measurable,
     and step 5 gives `I_(S₀)(φ, s) = κ · archimedeanOpenCellIntegral ψ φ₀ s = c(s)`.

## Provenance

This is the part of the proof of F. Shahidi, *On certain L-functions*, Amer. J. Math. 103
(1981) (`shahidi-1981-certain-l`), Theorem 5.1, pp. 351–352 (PDF pages 56–57), at the
finitely many places of `S` and the archimedean places, for the upper two-block parabolic of
`GL_(r+t+2)`. Shahidi writes the semilocal factor as the product `∏_(v ∈ S) W_v(e_v)` of
local values for a factorizable section; the archimedean factors continue analytically by
Proposition 3.2 (p. 333, PDF page 38), the finite ones by Proposition 3.1 (p. 332, PDF page
37), and the local data may be chosen with `W_v(e_v) ≠ 0` (p. 352).

The archimedean part is the premise `CuspidalPairEisensteinArchimedeanNumeratorStatement`.
At the finite places of `S₀` the Lean proof does not use Proposition 3.1: at each of these
places the section is cut off to the matrices `p w u'(y)` whose open-cell coordinate `y` lies
in a small ball around `0`, a neighbourhood of the coset `P w` in the open chart `P w U'` of
`P \ G` (corresponding to `u'(0) = 1` in `U'`). This makes the contribution of the finite
places the indicator of the matrices that are small at `S₀`, and the measure comparison turns
it into the nonzero constant `κ`. The choice of `S₀`
containing the set `T_ψ` of step 1 (outside which the components of `ψ` are trivial on the
integers) and the set `S₁` (outside which the section of the premise is spherical)
corresponds to Shahidi's choice of `S` on p. 351. The splitting into the cutoff, the finite
translation and the measure comparison is internal to the Library.
