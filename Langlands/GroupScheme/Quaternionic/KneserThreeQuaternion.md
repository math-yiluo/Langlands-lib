# Quaternion data from an orthogonal involution and a symmetric element

Module `Langlands.GroupScheme.Quaternionic.KneserThreeQuaternion`, namespaces
`Langlands.GroupScheme.KneserThree.QuatData` (generic part) and
`Langlands.GroupScheme.KneserThree.Quaternion`. This is internal support for the explicit A₃ = D₃
comparison used to prove `KneserThreeSpinSubgroupStatement` (Kneser's argument as summarized in
Tits, Bourbaki 505, 1977, no. 1.1.6). It makes no literature claim beyond what is proved here.

Let `D` be a finite-dimensional central division algebra over a field `K`, with `dim_K D = 4`
(`hdim`) and an involution of the first kind `σ` whose symmetric part has dimension `3` (`hsym`).
Let `μ` be a nonzero `σ`-symmetric element of `D`, and assume `2 ≠ 0` in `K`. The module builds
`Quaternion.quatData σ hdim hsym h2 hμ hμ0 : QuatData K D` (structure of
`KneserThreeSplitting`). It proves the facts that the exterior-square morphism of
`KneserThreeModelHom` and the binary morphism of `KneserThreeBinary` need from this data.

## Generic part (namespace `QuatData`, `D` a division ring)

For `Q : QuatData K D`, `L = field Q.c` and `ā` the Library's conjugation of `L`:

* `elem_mul_bar`: `(ι a + j ι a') · Q.bar (ι a + j ι a') = ι (a ā - δ a' ā')`. Here `Q.bar` is
  the conjugation of `KneserThreeUnits` and `δ = algebraMap K L Q.δ`.
* `diagForm`: the Hermitian form over `L` with weights `![-1, δ]` (`diagForm_weight`). If
  `Q.δ ≠ 0` (`hδ`), `diagUnits hδ` are unit witnesses for the weights (`diagUnits_val`).
  `algebraMap_δ_ne_zero` is the image of `hδ` in `L`.
* `diagForm_isAnisotropic`: the form is anisotropic, i.e. `-x₀ x̄₀ + δ x₁ x̄₁ = 0` forces `x = 0`.
  Otherwise `δ = a ā` with `a = x₀/x₁ ≠ 0`. Then `u = j ι (ā⁻¹)` satisfies `u² = 1`, so
  `u = ±1` in the division ring `D`. But the second coordinate of `u` is `ā⁻¹ ≠ 0`, while that
  of `±1` is `0`.

## From `σ` and `μ` (namespace `Quaternion`)

`conj = σ.quaternionConjugation hdim hsym`, `ell = σ.quaternionAlternatingUnit hdim hsym` (written
`ℓ`), and `nrd a` is the Library's reduced norm of `1 ⊗ a`. The Library gives
`conj a = ℓ σ(a) ℓ⁻¹` (`conj_apply`) and `a · conj a = nrd a` (`mul_conj`).

* `sigma_ell`, `conj_ell`, `sigma_ell_inv`: `ℓ` and `ℓ⁻¹` are skew for `σ`, and `ℓ` is skew for
  `conj`. `conj_algebraMap` and `add_conj_mem` (`a + conj a` is a scalar) are also proved.
* `ell_mul_self`: `ℓ² = -nrd ℓ` is a scalar. `sigma_eq_conj`: `σ d = ℓ · conj d · ℓ⁻¹`, because
  `ℓ²` is central.
* `pure μ = -(μ ℓ⁻¹)`. `conj_pure`: it is `conj`-skew. `pure_mul_self`: its square is the
  scalar `-nrd (pure μ)`. `pure_ne_zero`, and `pure_ne_algebraMap`: it is not a scalar when
  `2 ≠ 0` (`two_ne_zero_D`). `exists_not_commute`: since `D` is central, some `y` does not commute
  with `pure μ`.
* `partner` is such a `y` (chosen), and `jay = x y - y x` with `x = pure μ`. Then `jay_ne_zero`,
  `jay_mul_pure` (`j x = -x j`), `conj_jay` (`conj j = -j`) and `jay_mul_self`
  (`j² = -nrd j`).
* `quadVectors = ![1, x, j, j x]`. `linearIndependent_quadVectors` holds, and `quadBasis` is the
  resulting `K`-basis of `D` (using `dim D = 4`); `quadBasis_apply` gives its vectors.
* `pure_sq_ne`: `r² ≠ -nrd x` for every `r : K`, since otherwise `(x - r)(x + r) = 0` would make
  `x` a scalar.
* `quatData`: `c = -nrd x`, `δ = -nrd j`, `x`, `j`, with the relations above and the basis
  `quadBasis`. Irreducibility of `X² - c` comes from `pure_sq_ne` (`QuadField.irreducible_poly`),
  and separability from `QuadField.isSeparable` (`2 ≠ 0`, `c ≠ 0`). `quatData_x` and
  `quatData_j` record `x` and `j`. `quatData_δ_ne_zero`: `δ ≠ 0`, because `j ≠ 0`.

## Properties of `Q = quatData σ hdim hsym h2 hμ hμ0`

* `conj_ι`: `conj (ι a) = ι ā`. `conj_eq_bar`: `conj d = Q.bar d` for all `d`. This follows from
  `d = ι a + j ι a'`, anti-multiplicativity, `conj x = -x`, `conj j = -j` and `j ι a = ι ā j`.
* `lOne`, `lTwo` are the coordinates of `ℓ`. `elem_lOne_lTwo`: `ι l₁ + j ι l₂ = ℓ`.
  `conjugation_lOne`: `l̄₁ = -l₁`, from `Q.bar ℓ = conj ℓ = -ℓ`.
* `sigma_eq_bar`: `σ d = (ι l₁ + j ι l₂) · Q.bar d · ℓ⁻¹`. This is the hypothesis `hσ` of
  `QuatData.modelHom`.
* `neg_ι_root_mul_elem`: with `θ = root`, `-(ι θ · (ι l₁ + j ι l₂)) = μ`, since
  `ι root = x = -μ ℓ⁻¹`.
* `root_ne_zero`: `root ≠ 0` (its square is `c ≠ 0`). `norm_lOne_lTwo_ne_zero`:
  `l₁ l̄₁ - δ l₂ l̄₂ ≠ 0`, because by `elem_mul_bar` its image under `ι` is
  `ℓ · conj ℓ = -ℓ² ≠ 0`. These give the unit hypothesis `hw` of `modelHom`, with
  `w = (θ (l₁ l̄₁ - δ l₂ l̄₂))⁻¹`.
