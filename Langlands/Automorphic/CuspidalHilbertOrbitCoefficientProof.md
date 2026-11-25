# Proof of smooth actual determinant-band Hilbert orbit coefficients

Lean module: `Langlands.Automorphic.CuspidalHilbertOrbitCoefficientProof`.

The final theorem `Langlands.Automorphic.cuspidalHilbertOrbitCoefficient` proves the
Library statement `Langlands.Automorphic.CuspidalHilbertOrbitCoefficientStatement.{u}`.
It uses the helper module
`Langlands.Automorphic.CuspidalHilbertOrbitCoefficientJointFinite`, which has its own
Markdown, for the joint-finiteness conclusion.

The proof does not use the premise
`HasUnitaryCentralCharacter T`, nor irreducibility of `T`. It needs only cuspidality
(`T.cuspidal`) and the existing compact `AdeleQuotient F` convention. All the declarations
below are proved for an arbitrary operator realization `S` of `GL_n` with cuspidality
hypothesis `hS : S.IsCuspidal`. The final theorem applies them with `S = T.realization`
and `n = r + 1`.

## Notation

Write `μ` for `(quotientHaarMeasure F n).restrict (band F n)`. This is definitionally
`CuspidalHilbertOrbitCoefficient.bandMeasure F r` when `n = r + 1`. Fix `w` in `Lp ℂ 2 μ`,
and for `h : S.Space` write `h̄ = toQuotient F n S h`.

All definitions in this module are internal tools of the proof. Their provenance is the
construction described here.

## Translates over a compact set (section `CompactSup`)

- `continuous_toQuotient_translate₂`: `(q, c) ↦ h̄(translate c q)` is jointly continuous.
  Proof: lift through the open quotient map `LeftCosetSpace.mk × id`. There the function
  is `evaluate (S.toContinuous h) (x * c)`.
- `compactSup S Γ h q := sSup {‖h̄(translate c q)‖ | c ∈ Γ}`. For compact `Γ` it is
  continuous (`IsCompact.continuous_sSup`). It dominates every `‖h̄(translate c q)‖`
  with `c ∈ Γ` (`norm_le_compactSup`), and for nonempty `Γ` the supremum is attained
  (`exists_compactSup_eq`).
- `memLp_compactSup`: for cuspidal `S`, compact nonempty `Γ` and every `h`,
  `compactSup S Γ h` is in `L²(μ)`. Proof: the Library lemma
  `OperatorRealization.exists_band_cover_uniform` (with `lo = 1`, `hi = 2`) gives a
  measurable set `t` of adelic matrices meeting every rational coset over the band. It
  also gives a finite integral `∫⁻ x in t, Φ x ^ 2 ∂ν`, with respect to the matrix Haar
  measure, for every `Φ` bounded pointwise by some translate
  `‖evaluate (S.toContinuous h) (x * c)‖ₑ`, `c ∈ Γ`. Take
  `Φ x = ‖compactSup S Γ h (point x)‖ₑ`. Because the supremum is attained
  (`exists_compactSup_eq`), `Φ x` equals such a translate. The Library lemma
  `memLp_band_of_continuous` then gives membership.

## Matrix coordinates (sections `Coordinates`, `CoordFunctional`)

- `unitSet F n` is the open set of invertible archimedean matrices, the range of
  `Units.val`. Openness comes from `unitsChart`.
- `unitPoint F n y` is `(archimedeanGLCoordinates F n).symm` applied to the unit given by
  the inverse of `unitsChart`. `adelicPoint F n y = AdelicGL.ofInfinite F n (unitPoint F n y)`.
  Both are continuous on `unitSet`, and `unitPoint (v : Matrix) = coordinates.symm v`
  (`unitPoint_val`).
- `toQuotient_translate_unit`: at a quotient point represented by `x`,
  `h̄(translate (adelicPoint v) (point x))` equals the coordinate extension of the
  finite smooth slice of `h` at `finite x`, evaluated at the matrix `A · v`. Here
  `A` is the matrix of `infinite x`.
- `toQuotient_lieOperator_translate_unit`: the Lie derivative `S.lieOperator Z h`,
  evaluated at the same translated point, is the Fréchet derivative of that coordinate
  extension at `A · v` in the direction `(A · v) · Z` (via `evaluate_lieOperator_pair`).
- `toQuotient_lieOperator_eq_sum`: for a matrix `Z`, the quotient function of
  `S.lieOperator (realLieAlgebraToMatrix.symm Z) h` is `Σ_k c_k(Z) · (S.lieOperator X_k h)‾`,
  where `c_k` are the coordinates in `lieBasis F n` and `X_k = lieDirection F n k`
  (Library `smoothDifferential_val_eq_sum`).
- `coordFunctional F n k y` is the real functional `Y ↦ c_k(Ring.inverse y · Y)`. It is the
  continuous bilinear map `coordMap F n k` applied to `Ring.inverse y`, so it is `C^m` on
  `unitSet` for every `m` (`contDiffOn_coordFunctional`, from `contDiffAt_ringInverse`).
  At a unit `v`, `coordFunctional k v (v · Z) = c_k(Z)` (`coordFunctional_unit_mul`).

## Differentiation under the integral (section `Derivative`)

- `orbitCoefficient S w h g := ∫ ⟪w q, h̄(translate (ofInfinite g) q)⟫ dμ(q)`. With
  `S = T.realization` this is definitionally `CuspidalHilbertOrbitCoefficient.coefficient T w h g`.
- `matrixIntegrand S w h y q := ⟪w q, h̄(translate (adelicPoint y) q)⟫` and
  `matrixCoefficient S w h y := ∫ matrixIntegrand S w h y q dμ(q)`. These are the
  integrand and coefficient as functions of a matrix `y`. At a unit `v`,
  `matrixCoefficient S w h v = orbitCoefficient S w h (coordinates.symm v)`
  (`matrixCoefficient_val`). Each `matrixIntegrand S w h y` is integrable by the Library
  theorem `integrable_inner_translate_of_cuspidal`.
- `integrandDeriv S w h y q := Σ_k (coordFunctional k y).smulRight (matrixIntegrand S w (S.lieOperator X_k h) y q)`
  and `matrixDeriv S w h y := Σ_k (coordFunctional k y).smulRight (matrixCoefficient S w (S.lieOperator X_k h) y)`.
  These are the candidate derivatives. At a unit `v`,
  `matrixDeriv S w h v (v · Z) = Σ_k c_k(Z) · matrixCoefficient S w (S.lieOperator X_k h) v`
  (`matrixDeriv_unit_mul`).
- `hasFDerivAt_matrixIntegrand`: for `y ∈ unitSet` and every `q`, the map
  `y' ↦ matrixIntegrand S w h y' q` has derivative `integrandDeriv S w h y q` at `y`.
  Proof: write `q = point x` and `y = v`. Near `v` the integrand is
  `conj(w q) · E(A · y')`, with `E` the coordinate extension of a smooth slice
  (`toQuotient_translate_unit`, using that `unitSet` is open). The chain rule with the
  linear map `y' ↦ A · y'` gives the derivative `Y ↦ conj(w q) · dE(A v)(A Y)`. Write
  `A Y = (A v)(v⁻¹ Y)`. Then `toQuotient_lieOperator_translate_unit` and
  `toQuotient_lieOperator_eq_sum`, with `Z = v⁻¹ Y`, rewrite this as
  `Σ_k c_k(v⁻¹ Y) · matrixIntegrand S w (S.lieOperator X_k h) v q`.
- `norm_integrandDeriv_le`: if `‖coordFunctional k y‖ ≤ Cb k` on a set `s`, then for
  `y ∈ s` we have `‖integrandDeriv S w h y q‖ ≤ Σ_k Cb k · ‖w q‖ · compactSup_k(q)`. Here
  `compactSup_k = compactSup S (adelicPoint '' s) (S.lieOperator X_k h)`. This uses
  Cauchy–Schwarz and `norm_le_compactSup`.
- `integral_integrandDeriv`: `∫ integrandDeriv S w h y q dμ = matrixDeriv S w h y`. It
  follows from `integral_finsetSum` and `ContinuousLinearMap.integral_comp_comm` for
  the continuous linear map `smulRightL (coordFunctional k y)`.
  `aestronglyMeasurable_integrandDeriv` gives the measurability needed below.
- `hasFDerivAt_matrixCoefficient`: for `y₀ ∈ unitSet`, `matrixCoefficient S w h` has
  Fréchet derivative `matrixDeriv S w h y₀` at `y₀`. Proof: choose a closed ball `s`
  around `y₀` inside `unitSet`. Its image under `adelicPoint` is compact, and the
  continuous functionals `coordFunctional k` are bounded on `s` by constants `Cb k`. The
  dominating function `Σ_k Cb k · ‖w‖ · compactSup_k` is integrable, because each term is
  a product of two `L²` functions (`MemLp.integrable_mul`, `memLp_compactSup`). Mathlib's
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` then applies, and
  `integral_integrandDeriv` identifies the integral of the derivatives.

## Smoothness (section `Smoothness`)

- `contDiffOn_matrixCoefficient`: for every natural `m` and every `h`,
  `matrixCoefficient S w h` is `C^m` on `unitSet`. The proof is by induction on `m`,
  for all `h` at once. The case `m = 0` is continuity from differentiability. In the
  successor case `contDiffOn_succ_iff_fderiv_of_isOpen` reduces to `fderiv` being `C^m`. On
  `unitSet`, `fderiv` equals `matrixDeriv S w h`. This is a finite sum of
  `(coordFunctional k ·).smulRight (matrixCoefficient S w (S.lieOperator X_k h) ·)`, and it
  is `C^m` by `ContDiffOn.smulRight`, `contDiffOn_coordFunctional` and the induction
  hypothesis applied to the vectors `S.lieOperator X_k h`.
- `contDiffOn_infty_matrixCoefficient`: hence it is `C^∞` on `unitSet`.
- `orbitCoefficient_mem`: `orbitCoefficient S w h ∈ ArchimedeanGL.smoothFunctions F n`.
  Membership means smoothness of `v ↦ orbitCoefficient S w h (coordinates.symm v)` on the
  Lie group `ArchimedeanGL F n`. This function is `matrixCoefficient S w h ∘ Units.val`,
  and it is smooth by `contDiffOn_infty_matrixCoefficient` and `Units.contMDiff_val`.

## The coefficient map and covariance (section `Covariance`)

- `coefficientMap S w hS : S.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n` sends `h` to
  `⟨orbitCoefficient S w h, orbitCoefficient_mem⟩`. It is additive by `integral_add`, using
  the integrability `integrable_orbitIntegrand` (`integrable_inner_translate_of_cuspidal`).
  It is complex-homogeneous by `integral_const_mul`, since the inner product is linear in
  its second argument. Its values are `orbitCoefficient` by definition (`coefficientMap_val`).
- `matrixCoefficient_lieOperator_eq_sum`: integrating `toQuotient_lieOperator_eq_sum`
  gives `matrixCoefficient S w (S.lieOperator (realLieAlgebraToMatrix.symm Z) h) y = Σ_k c_k(Z) · matrixCoefficient S w (S.lieOperator X_k h) y`.
- `coefficientMap_lieOperator` (first-order covariance): for every real Lie algebra
  element `X`,
  `coefficientMap (S.lieOperator X h) = smoothDifferential F n X (coefficientMap h)`.
  Proof at `g`: let `v = archimedeanGLCoordinates g` and `M = realLieAlgebraToMatrix X`.
  `matrixCoefficient S w h` extends `coefficientMap h` from the units. By the Library lemma
  `smoothDifferential_eq_of_extension`, the right side is
  `fderiv (matrixCoefficient S w h) v (v · M)`. By `hasFDerivAt_matrixCoefficient` this
  is `matrixDeriv S w h v (v · M)`, which by `matrixDeriv_unit_mul` is
  `Σ_k c_k(M) · matrixCoefficient S w (S.lieOperator X_k h) v`. By
  `matrixCoefficient_lieOperator_eq_sum` and `realLieAlgebraToMatrix.symm M = X`, that
  sum is `matrixCoefficient S w (S.lieOperator X h) v`. This is the left side at `g`
  (`matrixCoefficient_val`, `coordinates.symm v = g`).
- `envelopingAction_generator_mul` and `smoothEnvelopingAction_generator_apply` are
  pointwise forms of `map_mul` and the Library `envelopingAction_real_generator`. Here
  `S.lieOperator X` is by definition `S.envelopingAction` of the generator of
  `complexify X`.
- `coefficientMap_envelopingAction` (genuine covariance): for every `a` in the enveloping
  algebra,
  `coefficientMap (S.envelopingAction a h) = ArchimedeanGL.envelopingAction F n a (coefficientMap h)`.
  The proof uses the Library induction principle `enveloping_real_left_induction`. The
  cases `1`, sums and complex scalars follow from the algebra-map properties of both
  actions. For `generator(complexify X) * a`, apply `envelopingAction_generator_mul`,
  then first-order covariance, then the induction hypothesis for `a`, and finally
  `smoothEnvelopingAction_generator_apply` and `envelopingAction_mul`.

## Final theorem

`Langlands.Automorphic.cuspidalHilbertOrbitCoefficient : CuspidalHilbertOrbitCoefficientStatement.{u}`
applies `cuspidalHilbertOrbitCoefficientStatement_of_covariant` from the helper module.
That reduction adds the joint-finiteness conclusion via `isJointFinite_of_covariant`.
For `F`, `r`, `T` and `w`, the proof supplies:

1. integrability of every `integrand T w f g`, by `integrable_orbitIntegrand T.realization w T.cuspidal f g`;
2. `C = coefficientMap T.realization w T.cuspidal`;
3. the values `(C f).val g = coefficient T w f g`, by `rfl`;
4. genuine covariance, by `coefficientMap_envelopingAction T.realization w T.cuspidal`.

## Notes

The file sets `backward.isDefEq.respectTransparency false` and opens
`Matrix.Norms.Operator` and `CategoryTheory.MonObj`, as the Library archimedean `GL`
modules do. It declares the same local `AddCommGroup` instances (`Submodule.addCommGroup _`)
as the statement module, together with the scheme instances `IsAffine` and `Smooth`
for `matrixGroupScheme F n`. No declaration in this module raises `maxHeartbeats`.
