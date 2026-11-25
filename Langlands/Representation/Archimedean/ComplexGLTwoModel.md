# Bottom-row functions on `GL_2(ℂ)` and their right derivatives

Lean module: `Langlands.Representation.Archimedean.ComplexGLTwoModel` (namespace
`Langlands.Archimedean.GLTwoModel`). It serves the proof of
`ComplexGLTwoUnlinkedIrreducibleStatement` (module `ComplexGLTwoUnlinkedIrreducibleProof`).

Provenance: internal infrastructure, derived. It realizes the polynomials of
`ComplexGLTwoPolynomial` as functions on `GL_2(ℂ)` and computes the action of
`complexStandardLie 2 ds` on them.

## Definitions

* `row M` is the bottom row of a `2 × 2` matrix, and `nrm r = |r₀|² + |r₁|²`.
* `realize Φ s P M = Φ(det M) · (nrm (row M))^s · P(r, r̄)` (`r = row M`, complex power of the
  positive real `nrm r`). `IsRealized Φ s P f` means `f g = realize Φ s P g` for all
  `g ∈ GL_2(ℂ)`.
* `zX X k`, `wX X k`, `Lpol X`, `Tpol X P`, `stepPol X s P = s · Lpol X · P + N · Tpol X P`: the
  polynomials of the derivative along `r ↦ r X`.
* `hol X = ½ ⊗ X - (i/2) ⊗ (iX)` and `antihol X = ½ ⊗ X + (i/2) ⊗ (iX)` in `ℂ ⊗_ℝ 𝔤𝔩_2(ℂ)`;
  `E01`, `E10`, `Ed = E₀₀ - E₁₁`; `k01 = hol E01 - antihol E10`, `k10 = hol E10 - antihol E01`,
  `kd = hol Ed - antihol Ed`; `casOp ds = 2(π k01 π k10 + π k10 π k01) + π kd π kd` with
  `π = complexStandardLie 2 ds`.
* `bottomMat r = !![r̄₁, -r̄₀; r₀, r₁]` (bottom row `r`, determinant `|r|²`).

## Main results

* `rightDerivative_realize`: if `f` is smooth on `GL_2(ℂ)`, `IsRealized Φ s P f`, `X` is traceless
  and `Φ` is real differentiable at `det g`, then
  `rightDerivative X f g = realize Φ (s - 1) (stepPol X s P) g`.
* `isRealized_hol`, `isRealized_antihol`: for `x` in the `U(2)`-finite functions `KF2 ds` with
  `IsRealized Φ s P x` and traceless `X`, `π(hol X) x` is realized at `s - 1` by
  `s (holZ X) P + N (holT X P)`, and `π(antihol X) x` by `s (antiZ X) P + N (antiT X P)`.
  Here `holZ X = Σ w_l (zX)_l`, `holT X = Σ (zX)_l ∂_{z_l}`, and `antiZ`, `antiT` are the conjugate
  versions.
* `isRealized_k01`, `isRealized_k10`, `isRealized_kd`: these act at the same exponent `s` by
  `D 0 1`, `D 1 0`, `D 0 0 - D 1 1`. `isRealized_casOp`: `casOp ds` acts by `Cas`.
* `eq_zero_of_isRealized_zero`: if `Φ` does not vanish on `ℂˣ` and `realize Φ s Q` vanishes on
  `GL_2(ℂ)`, then `Q = 0`.

## Proofs

`rightDerivative_realize` uses the Library lemma `rightDerivative_eq_fderiv`: the right
derivative is `fderiv (unitsExtension f) M (M X)`. This equals the derivative at `0` of
`t ↦ realize Φ s P (M + t M X)` (the two functions agree near `0`, where `M + t M X` is invertible).
Along this line, `det(M + tMX) = det M (1 + t² det X)` for traceless `X` (`det_line`), so the
`Φ(det)` factor has derivative `0`. The bottom row moves linearly, `r + t r X` (`row_line`). The
polynomial factor is differentiated by induction on the polynomial (`hasDerivAt_eval_curve`). The
power `nrm^s` is differentiated with `Complex.hasStrictDerivAt_cpow_const` at the positive real
`nrm r`. Then `N^s = N^{s-1} N` gives the stated form. The complexified moves follow from
`complexStandardLie (c ⊗ X) = c · rightDerivative X` (`coe_lie_tmul`). They also use the identities
`zX (iX) = i zX X`, `wX (iX) = -i wX X` (`stepPol_I_smul`) and `realize Φ s (N Q) = realize Φ (s+1) Q`.
Injectivity evaluates at `bottomMat r` for each `r ≠ 0` and applies `eq_zero_of_ev`.
